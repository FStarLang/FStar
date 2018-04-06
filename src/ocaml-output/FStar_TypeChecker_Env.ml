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
    match projectee with | Binding_var _0 -> true | uu____43 -> false
  
let (__proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____59 -> false
  
let (__proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_sig : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____89 -> false
  
let (__proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____119 -> false
  
let (__proj__Binding_univ__item___0 :
  binding -> FStar_Syntax_Syntax.univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Binding_sig_inst : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____139 -> false
  
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
    match projectee with | NoDelta  -> true | uu____178 -> false
  
let (uu___is_Inlining : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____182 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____186 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____191 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
let (uu___is_UnfoldTac : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____202 -> false
  
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
  init: env -> Prims.unit ;
  push: Prims.string -> Prims.unit ;
  pop: Prims.string -> Prims.unit ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit ;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
    ;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
    ;
  finish: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit }[@@deriving show]
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
  tc_push_in_gamma_hook: env -> binding -> Prims.unit }[@@deriving show]
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
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
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
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> Prims.unit -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh :
  solver_t -> Prims.unit -> Prims.unit) =
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
  tcenv_hooks -> env -> binding -> Prims.unit) =
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
           (fun uu___73_6379  ->
              match uu___73_6379 with
              | Binding_var x ->
                  let y =
                    let uu____6382 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____6382  in
                  let uu____6383 =
                    let uu____6384 = FStar_Syntax_Subst.compress y  in
                    uu____6384.FStar_Syntax_Syntax.n  in
                  (match uu____6383 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____6388 =
                         let uu___88_6389 = y1  in
                         let uu____6390 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___88_6389.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___88_6389.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____6390
                         }  in
                       Binding_var uu____6388
                   | uu____6393 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___89_6401 = env  in
      let uu____6402 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___89_6401.solver);
        range = (uu___89_6401.range);
        curmodule = (uu___89_6401.curmodule);
        gamma = uu____6402;
        gamma_cache = (uu___89_6401.gamma_cache);
        modules = (uu___89_6401.modules);
        expected_typ = (uu___89_6401.expected_typ);
        sigtab = (uu___89_6401.sigtab);
        is_pattern = (uu___89_6401.is_pattern);
        instantiate_imp = (uu___89_6401.instantiate_imp);
        effects = (uu___89_6401.effects);
        generalize = (uu___89_6401.generalize);
        letrecs = (uu___89_6401.letrecs);
        top_level = (uu___89_6401.top_level);
        check_uvars = (uu___89_6401.check_uvars);
        use_eq = (uu___89_6401.use_eq);
        is_iface = (uu___89_6401.is_iface);
        admit = (uu___89_6401.admit);
        lax = (uu___89_6401.lax);
        lax_universes = (uu___89_6401.lax_universes);
        failhard = (uu___89_6401.failhard);
        nosynth = (uu___89_6401.nosynth);
        tc_term = (uu___89_6401.tc_term);
        type_of = (uu___89_6401.type_of);
        universe_of = (uu___89_6401.universe_of);
        check_type_of = (uu___89_6401.check_type_of);
        use_bv_sorts = (uu___89_6401.use_bv_sorts);
        qtbl_name_and_index = (uu___89_6401.qtbl_name_and_index);
        normalized_eff_names = (uu___89_6401.normalized_eff_names);
        proof_ns = (uu___89_6401.proof_ns);
        synth_hook = (uu___89_6401.synth_hook);
        splice = (uu___89_6401.splice);
        is_native_tactic = (uu___89_6401.is_native_tactic);
        identifier_info = (uu___89_6401.identifier_info);
        tc_hooks = (uu___89_6401.tc_hooks);
        dsenv = (uu___89_6401.dsenv);
        dep_graph = (uu___89_6401.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____6409  -> fun uu____6410  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___90_6420 = env  in
      {
        solver = (uu___90_6420.solver);
        range = (uu___90_6420.range);
        curmodule = (uu___90_6420.curmodule);
        gamma = (uu___90_6420.gamma);
        gamma_cache = (uu___90_6420.gamma_cache);
        modules = (uu___90_6420.modules);
        expected_typ = (uu___90_6420.expected_typ);
        sigtab = (uu___90_6420.sigtab);
        is_pattern = (uu___90_6420.is_pattern);
        instantiate_imp = (uu___90_6420.instantiate_imp);
        effects = (uu___90_6420.effects);
        generalize = (uu___90_6420.generalize);
        letrecs = (uu___90_6420.letrecs);
        top_level = (uu___90_6420.top_level);
        check_uvars = (uu___90_6420.check_uvars);
        use_eq = (uu___90_6420.use_eq);
        is_iface = (uu___90_6420.is_iface);
        admit = (uu___90_6420.admit);
        lax = (uu___90_6420.lax);
        lax_universes = (uu___90_6420.lax_universes);
        failhard = (uu___90_6420.failhard);
        nosynth = (uu___90_6420.nosynth);
        tc_term = (uu___90_6420.tc_term);
        type_of = (uu___90_6420.type_of);
        universe_of = (uu___90_6420.universe_of);
        check_type_of = (uu___90_6420.check_type_of);
        use_bv_sorts = (uu___90_6420.use_bv_sorts);
        qtbl_name_and_index = (uu___90_6420.qtbl_name_and_index);
        normalized_eff_names = (uu___90_6420.normalized_eff_names);
        proof_ns = (uu___90_6420.proof_ns);
        synth_hook = (uu___90_6420.synth_hook);
        splice = (uu___90_6420.splice);
        is_native_tactic = (uu___90_6420.is_native_tactic);
        identifier_info = (uu___90_6420.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___90_6420.dsenv);
        dep_graph = (uu___90_6420.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___91_6427 = e  in
      {
        solver = (uu___91_6427.solver);
        range = (uu___91_6427.range);
        curmodule = (uu___91_6427.curmodule);
        gamma = (uu___91_6427.gamma);
        gamma_cache = (uu___91_6427.gamma_cache);
        modules = (uu___91_6427.modules);
        expected_typ = (uu___91_6427.expected_typ);
        sigtab = (uu___91_6427.sigtab);
        is_pattern = (uu___91_6427.is_pattern);
        instantiate_imp = (uu___91_6427.instantiate_imp);
        effects = (uu___91_6427.effects);
        generalize = (uu___91_6427.generalize);
        letrecs = (uu___91_6427.letrecs);
        top_level = (uu___91_6427.top_level);
        check_uvars = (uu___91_6427.check_uvars);
        use_eq = (uu___91_6427.use_eq);
        is_iface = (uu___91_6427.is_iface);
        admit = (uu___91_6427.admit);
        lax = (uu___91_6427.lax);
        lax_universes = (uu___91_6427.lax_universes);
        failhard = (uu___91_6427.failhard);
        nosynth = (uu___91_6427.nosynth);
        tc_term = (uu___91_6427.tc_term);
        type_of = (uu___91_6427.type_of);
        universe_of = (uu___91_6427.universe_of);
        check_type_of = (uu___91_6427.check_type_of);
        use_bv_sorts = (uu___91_6427.use_bv_sorts);
        qtbl_name_and_index = (uu___91_6427.qtbl_name_and_index);
        normalized_eff_names = (uu___91_6427.normalized_eff_names);
        proof_ns = (uu___91_6427.proof_ns);
        synth_hook = (uu___91_6427.synth_hook);
        splice = (uu___91_6427.splice);
        is_native_tactic = (uu___91_6427.is_native_tactic);
        identifier_info = (uu___91_6427.identifier_info);
        tc_hooks = (uu___91_6427.tc_hooks);
        dsenv = (uu___91_6427.dsenv);
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
      | (NoDelta ,uu____6442) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____6443,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____6444,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____6445 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____6452 . Prims.unit -> 'Auu____6452 FStar_Util.smap =
  fun uu____6458  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____6461 . Prims.unit -> 'Auu____6461 FStar_Util.smap =
  fun uu____6467  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____6563 = new_gamma_cache ()  in
                let uu____6566 = new_sigtab ()  in
                let uu____6569 =
                  let uu____6582 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____6582, FStar_Pervasives_Native.None)  in
                let uu____6597 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____6600 = FStar_Options.using_facts_from ()  in
                let uu____6601 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____6604 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____6563;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____6566;
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
                  qtbl_name_and_index = uu____6569;
                  normalized_eff_names = uu____6597;
                  proof_ns = uu____6600;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____6640  -> false);
                  identifier_info = uu____6601;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____6604;
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
let (push_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6723  ->
    let uu____6724 = FStar_ST.op_Bang query_indices  in
    match uu____6724 with
    | [] -> failwith "Empty query indices!"
    | uu____6774 ->
        let uu____6783 =
          let uu____6792 =
            let uu____6799 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____6799  in
          let uu____6849 = FStar_ST.op_Bang query_indices  in uu____6792 ::
            uu____6849
           in
        FStar_ST.op_Colon_Equals query_indices uu____6783
  
let (pop_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6936  ->
    let uu____6937 = FStar_ST.op_Bang query_indices  in
    match uu____6937 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____7050  ->
    match uu____7050 with
    | (l,n1) ->
        let uu____7057 = FStar_ST.op_Bang query_indices  in
        (match uu____7057 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____7168 -> failwith "Empty query indices")
  
let (peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____7185  ->
    let uu____7186 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____7186
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____7257 =
       let uu____7260 = FStar_ST.op_Bang stack  in env :: uu____7260  in
     FStar_ST.op_Colon_Equals stack uu____7257);
    (let uu___92_7309 = env  in
     let uu____7310 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____7313 = FStar_Util.smap_copy (sigtab env)  in
     let uu____7316 =
       let uu____7329 =
         let uu____7332 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____7332  in
       let uu____7357 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____7329, uu____7357)  in
     let uu____7398 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____7401 =
       let uu____7404 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____7404  in
     {
       solver = (uu___92_7309.solver);
       range = (uu___92_7309.range);
       curmodule = (uu___92_7309.curmodule);
       gamma = (uu___92_7309.gamma);
       gamma_cache = uu____7310;
       modules = (uu___92_7309.modules);
       expected_typ = (uu___92_7309.expected_typ);
       sigtab = uu____7313;
       is_pattern = (uu___92_7309.is_pattern);
       instantiate_imp = (uu___92_7309.instantiate_imp);
       effects = (uu___92_7309.effects);
       generalize = (uu___92_7309.generalize);
       letrecs = (uu___92_7309.letrecs);
       top_level = (uu___92_7309.top_level);
       check_uvars = (uu___92_7309.check_uvars);
       use_eq = (uu___92_7309.use_eq);
       is_iface = (uu___92_7309.is_iface);
       admit = (uu___92_7309.admit);
       lax = (uu___92_7309.lax);
       lax_universes = (uu___92_7309.lax_universes);
       failhard = (uu___92_7309.failhard);
       nosynth = (uu___92_7309.nosynth);
       tc_term = (uu___92_7309.tc_term);
       type_of = (uu___92_7309.type_of);
       universe_of = (uu___92_7309.universe_of);
       check_type_of = (uu___92_7309.check_type_of);
       use_bv_sorts = (uu___92_7309.use_bv_sorts);
       qtbl_name_and_index = uu____7316;
       normalized_eff_names = uu____7398;
       proof_ns = (uu___92_7309.proof_ns);
       synth_hook = (uu___92_7309.synth_hook);
       splice = (uu___92_7309.splice);
       is_native_tactic = (uu___92_7309.is_native_tactic);
       identifier_info = uu____7401;
       tc_hooks = (uu___92_7309.tc_hooks);
       dsenv = (uu___92_7309.dsenv);
       dep_graph = (uu___92_7309.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____7448  ->
    let uu____7449 = FStar_ST.op_Bang stack  in
    match uu____7449 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____7503 -> failwith "Impossible: Too many pops"
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____7532,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____7564 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____7590  ->
                  match uu____7590 with
                  | (m,uu____7596) -> FStar_Ident.lid_equals l m))
           in
        (match uu____7564 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___93_7604 = env  in
               {
                 solver = (uu___93_7604.solver);
                 range = (uu___93_7604.range);
                 curmodule = (uu___93_7604.curmodule);
                 gamma = (uu___93_7604.gamma);
                 gamma_cache = (uu___93_7604.gamma_cache);
                 modules = (uu___93_7604.modules);
                 expected_typ = (uu___93_7604.expected_typ);
                 sigtab = (uu___93_7604.sigtab);
                 is_pattern = (uu___93_7604.is_pattern);
                 instantiate_imp = (uu___93_7604.instantiate_imp);
                 effects = (uu___93_7604.effects);
                 generalize = (uu___93_7604.generalize);
                 letrecs = (uu___93_7604.letrecs);
                 top_level = (uu___93_7604.top_level);
                 check_uvars = (uu___93_7604.check_uvars);
                 use_eq = (uu___93_7604.use_eq);
                 is_iface = (uu___93_7604.is_iface);
                 admit = (uu___93_7604.admit);
                 lax = (uu___93_7604.lax);
                 lax_universes = (uu___93_7604.lax_universes);
                 failhard = (uu___93_7604.failhard);
                 nosynth = (uu___93_7604.nosynth);
                 tc_term = (uu___93_7604.tc_term);
                 type_of = (uu___93_7604.type_of);
                 universe_of = (uu___93_7604.universe_of);
                 check_type_of = (uu___93_7604.check_type_of);
                 use_bv_sorts = (uu___93_7604.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___93_7604.normalized_eff_names);
                 proof_ns = (uu___93_7604.proof_ns);
                 synth_hook = (uu___93_7604.synth_hook);
                 splice = (uu___93_7604.splice);
                 is_native_tactic = (uu___93_7604.is_native_tactic);
                 identifier_info = (uu___93_7604.identifier_info);
                 tc_hooks = (uu___93_7604.tc_hooks);
                 dsenv = (uu___93_7604.dsenv);
                 dep_graph = (uu___93_7604.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____7617,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___94_7626 = env  in
               {
                 solver = (uu___94_7626.solver);
                 range = (uu___94_7626.range);
                 curmodule = (uu___94_7626.curmodule);
                 gamma = (uu___94_7626.gamma);
                 gamma_cache = (uu___94_7626.gamma_cache);
                 modules = (uu___94_7626.modules);
                 expected_typ = (uu___94_7626.expected_typ);
                 sigtab = (uu___94_7626.sigtab);
                 is_pattern = (uu___94_7626.is_pattern);
                 instantiate_imp = (uu___94_7626.instantiate_imp);
                 effects = (uu___94_7626.effects);
                 generalize = (uu___94_7626.generalize);
                 letrecs = (uu___94_7626.letrecs);
                 top_level = (uu___94_7626.top_level);
                 check_uvars = (uu___94_7626.check_uvars);
                 use_eq = (uu___94_7626.use_eq);
                 is_iface = (uu___94_7626.is_iface);
                 admit = (uu___94_7626.admit);
                 lax = (uu___94_7626.lax);
                 lax_universes = (uu___94_7626.lax_universes);
                 failhard = (uu___94_7626.failhard);
                 nosynth = (uu___94_7626.nosynth);
                 tc_term = (uu___94_7626.tc_term);
                 type_of = (uu___94_7626.type_of);
                 universe_of = (uu___94_7626.universe_of);
                 check_type_of = (uu___94_7626.check_type_of);
                 use_bv_sorts = (uu___94_7626.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___94_7626.normalized_eff_names);
                 proof_ns = (uu___94_7626.proof_ns);
                 synth_hook = (uu___94_7626.synth_hook);
                 splice = (uu___94_7626.splice);
                 is_native_tactic = (uu___94_7626.is_native_tactic);
                 identifier_info = (uu___94_7626.identifier_info);
                 tc_hooks = (uu___94_7626.tc_hooks);
                 dsenv = (uu___94_7626.dsenv);
                 dep_graph = (uu___94_7626.dep_graph)
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
        (let uu___95_7652 = e  in
         {
           solver = (uu___95_7652.solver);
           range = r;
           curmodule = (uu___95_7652.curmodule);
           gamma = (uu___95_7652.gamma);
           gamma_cache = (uu___95_7652.gamma_cache);
           modules = (uu___95_7652.modules);
           expected_typ = (uu___95_7652.expected_typ);
           sigtab = (uu___95_7652.sigtab);
           is_pattern = (uu___95_7652.is_pattern);
           instantiate_imp = (uu___95_7652.instantiate_imp);
           effects = (uu___95_7652.effects);
           generalize = (uu___95_7652.generalize);
           letrecs = (uu___95_7652.letrecs);
           top_level = (uu___95_7652.top_level);
           check_uvars = (uu___95_7652.check_uvars);
           use_eq = (uu___95_7652.use_eq);
           is_iface = (uu___95_7652.is_iface);
           admit = (uu___95_7652.admit);
           lax = (uu___95_7652.lax);
           lax_universes = (uu___95_7652.lax_universes);
           failhard = (uu___95_7652.failhard);
           nosynth = (uu___95_7652.nosynth);
           tc_term = (uu___95_7652.tc_term);
           type_of = (uu___95_7652.type_of);
           universe_of = (uu___95_7652.universe_of);
           check_type_of = (uu___95_7652.check_type_of);
           use_bv_sorts = (uu___95_7652.use_bv_sorts);
           qtbl_name_and_index = (uu___95_7652.qtbl_name_and_index);
           normalized_eff_names = (uu___95_7652.normalized_eff_names);
           proof_ns = (uu___95_7652.proof_ns);
           synth_hook = (uu___95_7652.synth_hook);
           splice = (uu___95_7652.splice);
           is_native_tactic = (uu___95_7652.is_native_tactic);
           identifier_info = (uu___95_7652.identifier_info);
           tc_hooks = (uu___95_7652.tc_hooks);
           dsenv = (uu___95_7652.dsenv);
           dep_graph = (uu___95_7652.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____7662 =
        let uu____7663 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____7663 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7662
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____7711 =
          let uu____7712 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____7712 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7711
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____7760 =
          let uu____7761 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____7761 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7760
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____7811 =
        let uu____7812 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____7812 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7811
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___96_7865 = env  in
      {
        solver = (uu___96_7865.solver);
        range = (uu___96_7865.range);
        curmodule = lid;
        gamma = (uu___96_7865.gamma);
        gamma_cache = (uu___96_7865.gamma_cache);
        modules = (uu___96_7865.modules);
        expected_typ = (uu___96_7865.expected_typ);
        sigtab = (uu___96_7865.sigtab);
        is_pattern = (uu___96_7865.is_pattern);
        instantiate_imp = (uu___96_7865.instantiate_imp);
        effects = (uu___96_7865.effects);
        generalize = (uu___96_7865.generalize);
        letrecs = (uu___96_7865.letrecs);
        top_level = (uu___96_7865.top_level);
        check_uvars = (uu___96_7865.check_uvars);
        use_eq = (uu___96_7865.use_eq);
        is_iface = (uu___96_7865.is_iface);
        admit = (uu___96_7865.admit);
        lax = (uu___96_7865.lax);
        lax_universes = (uu___96_7865.lax_universes);
        failhard = (uu___96_7865.failhard);
        nosynth = (uu___96_7865.nosynth);
        tc_term = (uu___96_7865.tc_term);
        type_of = (uu___96_7865.type_of);
        universe_of = (uu___96_7865.universe_of);
        check_type_of = (uu___96_7865.check_type_of);
        use_bv_sorts = (uu___96_7865.use_bv_sorts);
        qtbl_name_and_index = (uu___96_7865.qtbl_name_and_index);
        normalized_eff_names = (uu___96_7865.normalized_eff_names);
        proof_ns = (uu___96_7865.proof_ns);
        synth_hook = (uu___96_7865.synth_hook);
        splice = (uu___96_7865.splice);
        is_native_tactic = (uu___96_7865.is_native_tactic);
        identifier_info = (uu___96_7865.identifier_info);
        tc_hooks = (uu___96_7865.tc_hooks);
        dsenv = (uu___96_7865.dsenv);
        dep_graph = (uu___96_7865.dep_graph)
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
      let uu____7884 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____7884
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____7892 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7892)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____7900 =
      let uu____7901 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7901  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7900)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____7904  ->
    let uu____7905 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7905
  
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
      | ((formals,t),uu____7943) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7967 = FStar_Syntax_Subst.subst vs t  in (us, uu____7967)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___74_7980  ->
    match uu___74_7980 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____8004  -> new_u_univ ()))
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
      let uu____8017 = inst_tscheme t  in
      match uu____8017 with
      | (us,t1) ->
          let uu____8028 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____8028)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____8040  ->
          match uu____8040 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____8055 =
                         let uu____8056 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____8057 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____8058 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____8059 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____8056 uu____8057 uu____8058 uu____8059
                          in
                       failwith uu____8055)
                    else ();
                    (let uu____8061 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____8061))
               | uu____8068 ->
                   let uu____8069 =
                     let uu____8070 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____8070
                      in
                   failwith uu____8069)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____8074 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____8078 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____8082 -> false
  
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
             | ([],uu____8116) -> Maybe
             | (uu____8123,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____8142 -> No  in
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
          let uu____8227 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____8227 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___75_8273  ->
                   match uu___75_8273 with
                   | Binding_lid (l,t) ->
                       let uu____8296 = FStar_Ident.lid_equals lid l  in
                       if uu____8296
                       then
                         let uu____8317 =
                           let uu____8336 =
                             let uu____8351 = inst_tscheme t  in
                             FStar_Util.Inl uu____8351  in
                           let uu____8366 = FStar_Ident.range_of_lid l  in
                           (uu____8336, uu____8366)  in
                         FStar_Pervasives_Native.Some uu____8317
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____8418,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____8420);
                                     FStar_Syntax_Syntax.sigrng = uu____8421;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____8422;
                                     FStar_Syntax_Syntax.sigmeta = uu____8423;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____8424;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____8444 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____8444
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____8490 ->
                             FStar_Pervasives_Native.Some t
                         | uu____8497 -> cache t  in
                       let uu____8498 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____8498 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____8540 =
                              let uu____8541 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                uu____8541)
                               in
                            maybe_cache uu____8540)
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____8575 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____8575 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____8617 =
                              let uu____8636 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                uu____8636)
                               in
                            FStar_Pervasives_Native.Some uu____8617)
                   | uu____8681 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____8741 = find_in_sigtab env lid  in
         match uu____8741 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8820) ->
          add_sigelts env ses
      | uu____8829 ->
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
            | uu____8843 -> ()))

and (add_sigelts :
  env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit) =
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
        (fun uu___76_8870  ->
           match uu___76_8870 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8888 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____8941,lb::[]),uu____8943) ->
            let uu____8956 =
              let uu____8965 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____8974 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____8965, uu____8974)  in
            FStar_Pervasives_Native.Some uu____8956
        | FStar_Syntax_Syntax.Sig_let ((uu____8987,lbs),uu____8989) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____9025 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____9037 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____9037
                     then
                       let uu____9048 =
                         let uu____9057 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____9066 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____9057, uu____9066)  in
                       FStar_Pervasives_Native.Some uu____9048
                     else FStar_Pervasives_Native.None)
        | uu____9088 -> FStar_Pervasives_Native.None
  
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
          let uu____9141 =
            let uu____9150 =
              let uu____9155 =
                let uu____9156 =
                  let uu____9159 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____9159
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____9156)  in
              inst_tscheme1 uu____9155  in
            (uu____9150, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____9141
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____9179,uu____9180) ->
          let uu____9185 =
            let uu____9194 =
              let uu____9199 =
                let uu____9200 =
                  let uu____9203 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____9203  in
                (us, uu____9200)  in
              inst_tscheme1 uu____9199  in
            (uu____9194, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____9185
      | uu____9220 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____9298 =
          match uu____9298 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____9394,uvs,t,uu____9397,uu____9398,uu____9399);
                      FStar_Syntax_Syntax.sigrng = uu____9400;
                      FStar_Syntax_Syntax.sigquals = uu____9401;
                      FStar_Syntax_Syntax.sigmeta = uu____9402;
                      FStar_Syntax_Syntax.sigattrs = uu____9403;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____9424 =
                     let uu____9433 = inst_tscheme1 (uvs, t)  in
                     (uu____9433, rng)  in
                   FStar_Pervasives_Native.Some uu____9424
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____9453;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____9455;
                      FStar_Syntax_Syntax.sigattrs = uu____9456;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____9473 =
                     let uu____9474 = in_cur_mod env l  in uu____9474 = Yes
                      in
                   if uu____9473
                   then
                     let uu____9485 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____9485
                      then
                        let uu____9498 =
                          let uu____9507 = inst_tscheme1 (uvs, t)  in
                          (uu____9507, rng)  in
                        FStar_Pervasives_Native.Some uu____9498
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9534 =
                        let uu____9543 = inst_tscheme1 (uvs, t)  in
                        (uu____9543, rng)  in
                      FStar_Pervasives_Native.Some uu____9534)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9564,uu____9565);
                      FStar_Syntax_Syntax.sigrng = uu____9566;
                      FStar_Syntax_Syntax.sigquals = uu____9567;
                      FStar_Syntax_Syntax.sigmeta = uu____9568;
                      FStar_Syntax_Syntax.sigattrs = uu____9569;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____9608 =
                          let uu____9617 = inst_tscheme1 (uvs, k)  in
                          (uu____9617, rng)  in
                        FStar_Pervasives_Native.Some uu____9608
                    | uu____9634 ->
                        let uu____9635 =
                          let uu____9644 =
                            let uu____9649 =
                              let uu____9650 =
                                let uu____9653 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9653
                                 in
                              (uvs, uu____9650)  in
                            inst_tscheme1 uu____9649  in
                          (uu____9644, rng)  in
                        FStar_Pervasives_Native.Some uu____9635)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9674,uu____9675);
                      FStar_Syntax_Syntax.sigrng = uu____9676;
                      FStar_Syntax_Syntax.sigquals = uu____9677;
                      FStar_Syntax_Syntax.sigmeta = uu____9678;
                      FStar_Syntax_Syntax.sigattrs = uu____9679;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____9719 =
                          let uu____9728 = inst_tscheme_with (uvs, k) us  in
                          (uu____9728, rng)  in
                        FStar_Pervasives_Native.Some uu____9719
                    | uu____9745 ->
                        let uu____9746 =
                          let uu____9755 =
                            let uu____9760 =
                              let uu____9761 =
                                let uu____9764 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9764
                                 in
                              (uvs, uu____9761)  in
                            inst_tscheme_with uu____9760 us  in
                          (uu____9755, rng)  in
                        FStar_Pervasives_Native.Some uu____9746)
               | FStar_Util.Inr se ->
                   let uu____9798 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____9819;
                          FStar_Syntax_Syntax.sigrng = uu____9820;
                          FStar_Syntax_Syntax.sigquals = uu____9821;
                          FStar_Syntax_Syntax.sigmeta = uu____9822;
                          FStar_Syntax_Syntax.sigattrs = uu____9823;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____9838 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____9798
                     (FStar_Util.map_option
                        (fun uu____9886  ->
                           match uu____9886 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____9917 =
          let uu____9928 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____9928 mapper  in
        match uu____9917 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____10002 =
              let uu____10013 =
                let uu____10020 =
                  let uu___97_10023 = t  in
                  let uu____10024 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___97_10023.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____10024;
                    FStar_Syntax_Syntax.vars =
                      (uu___97_10023.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____10020)  in
              (uu____10013, r)  in
            FStar_Pervasives_Native.Some uu____10002
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____10067 = lookup_qname env l  in
      match uu____10067 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____10086 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____10134 = try_lookup_bv env bv  in
      match uu____10134 with
      | FStar_Pervasives_Native.None  ->
          let uu____10149 = variable_not_found bv  in
          FStar_Errors.raise_error uu____10149 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____10164 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____10165 =
            let uu____10166 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____10166  in
          (uu____10164, uu____10165)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____10183 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____10183 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____10249 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____10249  in
          let uu____10250 =
            let uu____10259 =
              let uu____10264 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____10264)  in
            (uu____10259, r1)  in
          FStar_Pervasives_Native.Some uu____10250
  
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
        let uu____10292 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____10292 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____10325,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____10350 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____10350  in
            let uu____10351 =
              let uu____10356 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____10356, r1)  in
            FStar_Pervasives_Native.Some uu____10351
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____10375 = try_lookup_lid env l  in
      match uu____10375 with
      | FStar_Pervasives_Native.None  ->
          let uu____10402 = name_not_found l  in
          let uu____10407 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____10402 uu____10407
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___77_10443  ->
              match uu___77_10443 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____10445 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10460 = lookup_qname env lid  in
      match uu____10460 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10469,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____10472;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10474;
              FStar_Syntax_Syntax.sigattrs = uu____10475;_},FStar_Pervasives_Native.None
            ),uu____10476)
          ->
          let uu____10525 =
            let uu____10536 =
              let uu____10541 =
                let uu____10542 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____10542 t  in
              (uvs, uu____10541)  in
            (uu____10536, q)  in
          FStar_Pervasives_Native.Some uu____10525
      | uu____10559 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10576 = lookup_qname env lid  in
      match uu____10576 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10581,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____10584;
              FStar_Syntax_Syntax.sigquals = uu____10585;
              FStar_Syntax_Syntax.sigmeta = uu____10586;
              FStar_Syntax_Syntax.sigattrs = uu____10587;_},FStar_Pervasives_Native.None
            ),uu____10588)
          ->
          let uu____10637 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____10637 (uvs, t)
      | uu____10638 ->
          let uu____10639 = name_not_found lid  in
          let uu____10644 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____10639 uu____10644
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10659 = lookup_qname env lid  in
      match uu____10659 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10664,uvs,t,uu____10667,uu____10668,uu____10669);
              FStar_Syntax_Syntax.sigrng = uu____10670;
              FStar_Syntax_Syntax.sigquals = uu____10671;
              FStar_Syntax_Syntax.sigmeta = uu____10672;
              FStar_Syntax_Syntax.sigattrs = uu____10673;_},FStar_Pervasives_Native.None
            ),uu____10674)
          ->
          let uu____10727 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____10727 (uvs, t)
      | uu____10728 ->
          let uu____10729 = name_not_found lid  in
          let uu____10734 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____10729 uu____10734
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10751 = lookup_qname env lid  in
      match uu____10751 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10758,uu____10759,uu____10760,uu____10761,uu____10762,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10764;
              FStar_Syntax_Syntax.sigquals = uu____10765;
              FStar_Syntax_Syntax.sigmeta = uu____10766;
              FStar_Syntax_Syntax.sigattrs = uu____10767;_},uu____10768),uu____10769)
          -> (true, dcs)
      | uu____10830 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____10839 = lookup_qname env lid  in
      match uu____10839 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10840,uu____10841,uu____10842,l,uu____10844,uu____10845);
              FStar_Syntax_Syntax.sigrng = uu____10846;
              FStar_Syntax_Syntax.sigquals = uu____10847;
              FStar_Syntax_Syntax.sigmeta = uu____10848;
              FStar_Syntax_Syntax.sigattrs = uu____10849;_},uu____10850),uu____10851)
          -> l
      | uu____10906 ->
          let uu____10907 =
            let uu____10908 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10908  in
          failwith uu____10907
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10949)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____11000,lbs),uu____11002)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____11030 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____11030
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____11062 -> FStar_Pervasives_Native.None)
        | uu____11067 -> FStar_Pervasives_Native.None
  
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
        let uu____11091 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____11091
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____11114),uu____11115) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____11164 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____11181 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____11181
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____11196 = lookup_qname env ftv  in
      match uu____11196 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____11200) ->
          let uu____11245 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____11245 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____11266,t),r) ->
               let uu____11281 =
                 let uu____11282 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____11282 t  in
               FStar_Pervasives_Native.Some uu____11281)
      | uu____11283 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____11290 = try_lookup_effect_lid env ftv  in
      match uu____11290 with
      | FStar_Pervasives_Native.None  ->
          let uu____11293 = name_not_found ftv  in
          let uu____11298 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____11293 uu____11298
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
        let uu____11315 = lookup_qname env lid0  in
        match uu____11315 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____11326);
                FStar_Syntax_Syntax.sigrng = uu____11327;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____11329;
                FStar_Syntax_Syntax.sigattrs = uu____11330;_},FStar_Pervasives_Native.None
              ),uu____11331)
            ->
            let lid1 =
              let uu____11385 =
                let uu____11386 = FStar_Ident.range_of_lid lid  in
                let uu____11387 =
                  let uu____11388 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____11388  in
                FStar_Range.set_use_range uu____11386 uu____11387  in
              FStar_Ident.set_lid_range lid uu____11385  in
            let uu____11389 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___78_11393  ->
                      match uu___78_11393 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11394 -> false))
               in
            if uu____11389
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____11408 =
                      let uu____11409 =
                        let uu____11410 = get_range env  in
                        FStar_Range.string_of_range uu____11410  in
                      let uu____11411 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____11412 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____11409 uu____11411 uu____11412
                       in
                    failwith uu____11408)
                  in
               match (binders, univs1) with
               | ([],uu____11419) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____11436,uu____11437::uu____11438::uu____11439) ->
                   let uu____11444 =
                     let uu____11445 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____11446 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____11445 uu____11446
                      in
                   failwith uu____11444
               | uu____11453 ->
                   let uu____11458 =
                     let uu____11463 =
                       let uu____11464 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____11464)  in
                     inst_tscheme_with uu____11463 insts  in
                   (match uu____11458 with
                    | (uu____11475,t) ->
                        let t1 =
                          let uu____11478 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____11478 t  in
                        let uu____11479 =
                          let uu____11480 = FStar_Syntax_Subst.compress t1
                             in
                          uu____11480.FStar_Syntax_Syntax.n  in
                        (match uu____11479 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____11527 -> failwith "Impossible")))
        | uu____11534 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____11551 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____11551 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____11564,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____11571 = find1 l2  in
            (match uu____11571 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____11578 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____11578 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____11582 = find1 l  in
            (match uu____11582 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____11587 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____11587
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____11597 = lookup_qname env l1  in
      match uu____11597 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____11600;
              FStar_Syntax_Syntax.sigrng = uu____11601;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11603;
              FStar_Syntax_Syntax.sigattrs = uu____11604;_},uu____11605),uu____11606)
          -> q
      | uu____11657 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____11670 =
          let uu____11671 =
            let uu____11672 = FStar_Util.string_of_int i  in
            let uu____11673 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____11672 uu____11673
             in
          failwith uu____11671  in
        let uu____11674 = lookup_datacon env lid  in
        match uu____11674 with
        | (uu____11679,t) ->
            let uu____11681 =
              let uu____11682 = FStar_Syntax_Subst.compress t  in
              uu____11682.FStar_Syntax_Syntax.n  in
            (match uu____11681 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11686) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____11717 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____11717
                      FStar_Pervasives_Native.fst)
             | uu____11726 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11733 = lookup_qname env l  in
      match uu____11733 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11734,uu____11735,uu____11736);
              FStar_Syntax_Syntax.sigrng = uu____11737;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11739;
              FStar_Syntax_Syntax.sigattrs = uu____11740;_},uu____11741),uu____11742)
          ->
          FStar_Util.for_some
            (fun uu___79_11795  ->
               match uu___79_11795 with
               | FStar_Syntax_Syntax.Projector uu____11796 -> true
               | uu____11801 -> false) quals
      | uu____11802 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11809 = lookup_qname env lid  in
      match uu____11809 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11810,uu____11811,uu____11812,uu____11813,uu____11814,uu____11815);
              FStar_Syntax_Syntax.sigrng = uu____11816;
              FStar_Syntax_Syntax.sigquals = uu____11817;
              FStar_Syntax_Syntax.sigmeta = uu____11818;
              FStar_Syntax_Syntax.sigattrs = uu____11819;_},uu____11820),uu____11821)
          -> true
      | uu____11876 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11883 = lookup_qname env lid  in
      match uu____11883 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11884,uu____11885,uu____11886,uu____11887,uu____11888,uu____11889);
              FStar_Syntax_Syntax.sigrng = uu____11890;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11892;
              FStar_Syntax_Syntax.sigattrs = uu____11893;_},uu____11894),uu____11895)
          ->
          FStar_Util.for_some
            (fun uu___80_11956  ->
               match uu___80_11956 with
               | FStar_Syntax_Syntax.RecordType uu____11957 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11966 -> true
               | uu____11975 -> false) quals
      | uu____11976 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____11980,uu____11981);
            FStar_Syntax_Syntax.sigrng = uu____11982;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____11984;
            FStar_Syntax_Syntax.sigattrs = uu____11985;_},uu____11986),uu____11987)
        ->
        FStar_Util.for_some
          (fun uu___81_12044  ->
             match uu___81_12044 with
             | FStar_Syntax_Syntax.Action uu____12045 -> true
             | uu____12046 -> false) quals
    | uu____12047 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____12054 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____12054
  
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
      let uu____12064 =
        let uu____12065 = FStar_Syntax_Util.un_uinst head1  in
        uu____12065.FStar_Syntax_Syntax.n  in
      match uu____12064 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____12069 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12076 = lookup_qname env l  in
      match uu____12076 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____12078),uu____12079) ->
          FStar_Util.for_some
            (fun uu___82_12127  ->
               match uu___82_12127 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____12128 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____12129 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____12194 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____12210) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____12227 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____12234 ->
                 FStar_Pervasives_Native.Some true
             | uu____12251 -> FStar_Pervasives_Native.Some false)
         in
      let uu____12252 =
        let uu____12255 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____12255 mapper  in
      match uu____12252 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____12301 = lookup_qname env lid  in
      match uu____12301 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12302,uu____12303,tps,uu____12305,uu____12306,uu____12307);
              FStar_Syntax_Syntax.sigrng = uu____12308;
              FStar_Syntax_Syntax.sigquals = uu____12309;
              FStar_Syntax_Syntax.sigmeta = uu____12310;
              FStar_Syntax_Syntax.sigattrs = uu____12311;_},uu____12312),uu____12313)
          -> FStar_List.length tps
      | uu____12376 ->
          let uu____12377 = name_not_found lid  in
          let uu____12382 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12377 uu____12382
  
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
           (fun uu____12422  ->
              match uu____12422 with
              | (d,uu____12430) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____12441 = effect_decl_opt env l  in
      match uu____12441 with
      | FStar_Pervasives_Native.None  ->
          let uu____12456 = name_not_found l  in
          let uu____12461 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12456 uu____12461
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____12483  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____12498  ->
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
        let uu____12523 = FStar_Ident.lid_equals l1 l2  in
        if uu____12523
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____12531 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____12531
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____12539 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____12592  ->
                        match uu____12592 with
                        | (m1,m2,uu____12605,uu____12606,uu____12607) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____12539 with
              | FStar_Pervasives_Native.None  ->
                  let uu____12624 =
                    let uu____12629 =
                      let uu____12630 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____12631 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____12630
                        uu____12631
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____12629)
                     in
                  FStar_Errors.raise_error uu____12624 env.range
              | FStar_Pervasives_Native.Some
                  (uu____12638,uu____12639,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____12666 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____12666
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
  'Auu____12679 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12679)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12706 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12732  ->
                match uu____12732 with
                | (d,uu____12738) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____12706 with
      | FStar_Pervasives_Native.None  ->
          let uu____12749 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12749
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12762 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12762 with
           | (uu____12773,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12783)::(wp,uu____12785)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12821 -> failwith "Impossible"))
  
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
          let uu____12856 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____12856
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____12858 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____12858
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
                  let uu____12866 = get_range env  in
                  let uu____12867 =
                    let uu____12870 =
                      let uu____12871 =
                        let uu____12886 =
                          let uu____12889 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____12889]  in
                        (null_wp, uu____12886)  in
                      FStar_Syntax_Syntax.Tm_app uu____12871  in
                    FStar_Syntax_Syntax.mk uu____12870  in
                  uu____12867 FStar_Pervasives_Native.None uu____12866  in
                let uu____12895 =
                  let uu____12896 =
                    let uu____12905 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____12905]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____12896;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____12895))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___98_12914 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___98_12914.order);
              joins = (uu___98_12914.joins)
            }  in
          let uu___99_12923 = env  in
          {
            solver = (uu___99_12923.solver);
            range = (uu___99_12923.range);
            curmodule = (uu___99_12923.curmodule);
            gamma = (uu___99_12923.gamma);
            gamma_cache = (uu___99_12923.gamma_cache);
            modules = (uu___99_12923.modules);
            expected_typ = (uu___99_12923.expected_typ);
            sigtab = (uu___99_12923.sigtab);
            is_pattern = (uu___99_12923.is_pattern);
            instantiate_imp = (uu___99_12923.instantiate_imp);
            effects;
            generalize = (uu___99_12923.generalize);
            letrecs = (uu___99_12923.letrecs);
            top_level = (uu___99_12923.top_level);
            check_uvars = (uu___99_12923.check_uvars);
            use_eq = (uu___99_12923.use_eq);
            is_iface = (uu___99_12923.is_iface);
            admit = (uu___99_12923.admit);
            lax = (uu___99_12923.lax);
            lax_universes = (uu___99_12923.lax_universes);
            failhard = (uu___99_12923.failhard);
            nosynth = (uu___99_12923.nosynth);
            tc_term = (uu___99_12923.tc_term);
            type_of = (uu___99_12923.type_of);
            universe_of = (uu___99_12923.universe_of);
            check_type_of = (uu___99_12923.check_type_of);
            use_bv_sorts = (uu___99_12923.use_bv_sorts);
            qtbl_name_and_index = (uu___99_12923.qtbl_name_and_index);
            normalized_eff_names = (uu___99_12923.normalized_eff_names);
            proof_ns = (uu___99_12923.proof_ns);
            synth_hook = (uu___99_12923.synth_hook);
            splice = (uu___99_12923.splice);
            is_native_tactic = (uu___99_12923.is_native_tactic);
            identifier_info = (uu___99_12923.identifier_info);
            tc_hooks = (uu___99_12923.tc_hooks);
            dsenv = (uu___99_12923.dsenv);
            dep_graph = (uu___99_12923.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12943 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12943  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____13057 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____13058 = l1 u t wp e  in
                                l2 u t uu____13057 uu____13058))
                | uu____13059 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____13107 = inst_tscheme_with lift_t [u]  in
            match uu____13107 with
            | (uu____13114,lift_t1) ->
                let uu____13116 =
                  let uu____13119 =
                    let uu____13120 =
                      let uu____13135 =
                        let uu____13138 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____13139 =
                          let uu____13142 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____13142]  in
                        uu____13138 :: uu____13139  in
                      (lift_t1, uu____13135)  in
                    FStar_Syntax_Syntax.Tm_app uu____13120  in
                  FStar_Syntax_Syntax.mk uu____13119  in
                uu____13116 FStar_Pervasives_Native.None
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
            let uu____13192 = inst_tscheme_with lift_t [u]  in
            match uu____13192 with
            | (uu____13199,lift_t1) ->
                let uu____13201 =
                  let uu____13204 =
                    let uu____13205 =
                      let uu____13220 =
                        let uu____13223 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____13224 =
                          let uu____13227 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____13228 =
                            let uu____13231 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____13231]  in
                          uu____13227 :: uu____13228  in
                        uu____13223 :: uu____13224  in
                      (lift_t1, uu____13220)  in
                    FStar_Syntax_Syntax.Tm_app uu____13205  in
                  FStar_Syntax_Syntax.mk uu____13204  in
                uu____13201 FStar_Pervasives_Native.None
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
              let uu____13273 =
                let uu____13274 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____13274
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____13273  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____13278 =
              let uu____13279 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____13279  in
            let uu____13280 =
              let uu____13281 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____13303 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____13303)
                 in
              FStar_Util.dflt "none" uu____13281  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____13278
              uu____13280
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____13329  ->
                    match uu____13329 with
                    | (e,uu____13337) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____13356 =
            match uu____13356 with
            | (i,j) ->
                let uu____13367 = FStar_Ident.lid_equals i j  in
                if uu____13367
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____13395 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____13405 = FStar_Ident.lid_equals i k  in
                        if uu____13405
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____13416 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____13416
                                  then []
                                  else
                                    (let uu____13420 =
                                       let uu____13429 =
                                         find_edge order1 (i, k)  in
                                       let uu____13432 =
                                         find_edge order1 (k, j)  in
                                       (uu____13429, uu____13432)  in
                                     match uu____13420 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____13447 =
                                           compose_edges e1 e2  in
                                         [uu____13447]
                                     | uu____13448 -> [])))))
                 in
              FStar_List.append order1 uu____13395  in
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
                   let uu____13478 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____13480 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____13480
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____13478
                   then
                     let uu____13485 =
                       let uu____13490 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____13490)
                        in
                     let uu____13491 = get_range env  in
                     FStar_Errors.raise_error uu____13485 uu____13491
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____13568 = FStar_Ident.lid_equals i j
                                   in
                                if uu____13568
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____13617 =
                                              let uu____13626 =
                                                find_edge order2 (i, k)  in
                                              let uu____13629 =
                                                find_edge order2 (j, k)  in
                                              (uu____13626, uu____13629)  in
                                            match uu____13617 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13671,uu____13672)
                                                     ->
                                                     let uu____13679 =
                                                       let uu____13684 =
                                                         let uu____13685 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13685
                                                          in
                                                       let uu____13688 =
                                                         let uu____13689 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13689
                                                          in
                                                       (uu____13684,
                                                         uu____13688)
                                                        in
                                                     (match uu____13679 with
                                                      | (true ,true ) ->
                                                          let uu____13700 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____13700
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
                                            | uu____13725 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___100_13798 = env.effects  in
              { decls = (uu___100_13798.decls); order = order2; joins }  in
            let uu___101_13799 = env  in
            {
              solver = (uu___101_13799.solver);
              range = (uu___101_13799.range);
              curmodule = (uu___101_13799.curmodule);
              gamma = (uu___101_13799.gamma);
              gamma_cache = (uu___101_13799.gamma_cache);
              modules = (uu___101_13799.modules);
              expected_typ = (uu___101_13799.expected_typ);
              sigtab = (uu___101_13799.sigtab);
              is_pattern = (uu___101_13799.is_pattern);
              instantiate_imp = (uu___101_13799.instantiate_imp);
              effects;
              generalize = (uu___101_13799.generalize);
              letrecs = (uu___101_13799.letrecs);
              top_level = (uu___101_13799.top_level);
              check_uvars = (uu___101_13799.check_uvars);
              use_eq = (uu___101_13799.use_eq);
              is_iface = (uu___101_13799.is_iface);
              admit = (uu___101_13799.admit);
              lax = (uu___101_13799.lax);
              lax_universes = (uu___101_13799.lax_universes);
              failhard = (uu___101_13799.failhard);
              nosynth = (uu___101_13799.nosynth);
              tc_term = (uu___101_13799.tc_term);
              type_of = (uu___101_13799.type_of);
              universe_of = (uu___101_13799.universe_of);
              check_type_of = (uu___101_13799.check_type_of);
              use_bv_sorts = (uu___101_13799.use_bv_sorts);
              qtbl_name_and_index = (uu___101_13799.qtbl_name_and_index);
              normalized_eff_names = (uu___101_13799.normalized_eff_names);
              proof_ns = (uu___101_13799.proof_ns);
              synth_hook = (uu___101_13799.synth_hook);
              splice = (uu___101_13799.splice);
              is_native_tactic = (uu___101_13799.is_native_tactic);
              identifier_info = (uu___101_13799.identifier_info);
              tc_hooks = (uu___101_13799.tc_hooks);
              dsenv = (uu___101_13799.dsenv);
              dep_graph = (uu___101_13799.dep_graph)
            }))
      | uu____13800 -> env
  
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
        | uu____13824 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13832 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13832 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13849 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13849 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13867 =
                     let uu____13872 =
                       let uu____13873 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13878 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13885 =
                         let uu____13886 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13886  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13873 uu____13878 uu____13885
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13872)
                      in
                   FStar_Errors.raise_error uu____13867
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13891 =
                     let uu____13900 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13900 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13917  ->
                        fun uu____13918  ->
                          match (uu____13917, uu____13918) with
                          | ((x,uu____13940),(t,uu____13942)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13891
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13961 =
                     let uu___102_13962 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___102_13962.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___102_13962.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___102_13962.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___102_13962.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13961
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
          let uu____13984 = effect_decl_opt env effect_name  in
          match uu____13984 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____14017 =
                only_reifiable &&
                  (let uu____14019 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____14019)
                 in
              if uu____14017
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____14035 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____14054 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____14083 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____14083
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____14084 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____14084
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____14094 =
                       let uu____14097 = get_range env  in
                       let uu____14098 =
                         let uu____14101 =
                           let uu____14102 =
                             let uu____14117 =
                               let uu____14120 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____14120; wp]  in
                             (repr, uu____14117)  in
                           FStar_Syntax_Syntax.Tm_app uu____14102  in
                         FStar_Syntax_Syntax.mk uu____14101  in
                       uu____14098 FStar_Pervasives_Native.None uu____14097
                        in
                     FStar_Pervasives_Native.Some uu____14094)
  
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
          let uu____14166 =
            let uu____14171 =
              let uu____14172 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____14172
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____14171)  in
          let uu____14173 = get_range env  in
          FStar_Errors.raise_error uu____14166 uu____14173  in
        let uu____14174 = effect_repr_aux true env c u_c  in
        match uu____14174 with
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
      | uu____14208 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____14215 =
        let uu____14216 = FStar_Syntax_Subst.compress t  in
        uu____14216.FStar_Syntax_Syntax.n  in
      match uu____14215 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____14219,c) ->
          is_reifiable_comp env c
      | uu____14237 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____14259)::uu____14260 -> x :: rest
        | (Binding_sig_inst uu____14269)::uu____14270 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____14285 = push1 x rest1  in local :: uu____14285
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___103_14289 = env  in
       let uu____14290 = push1 s env.gamma  in
       {
         solver = (uu___103_14289.solver);
         range = (uu___103_14289.range);
         curmodule = (uu___103_14289.curmodule);
         gamma = uu____14290;
         gamma_cache = (uu___103_14289.gamma_cache);
         modules = (uu___103_14289.modules);
         expected_typ = (uu___103_14289.expected_typ);
         sigtab = (uu___103_14289.sigtab);
         is_pattern = (uu___103_14289.is_pattern);
         instantiate_imp = (uu___103_14289.instantiate_imp);
         effects = (uu___103_14289.effects);
         generalize = (uu___103_14289.generalize);
         letrecs = (uu___103_14289.letrecs);
         top_level = (uu___103_14289.top_level);
         check_uvars = (uu___103_14289.check_uvars);
         use_eq = (uu___103_14289.use_eq);
         is_iface = (uu___103_14289.is_iface);
         admit = (uu___103_14289.admit);
         lax = (uu___103_14289.lax);
         lax_universes = (uu___103_14289.lax_universes);
         failhard = (uu___103_14289.failhard);
         nosynth = (uu___103_14289.nosynth);
         tc_term = (uu___103_14289.tc_term);
         type_of = (uu___103_14289.type_of);
         universe_of = (uu___103_14289.universe_of);
         check_type_of = (uu___103_14289.check_type_of);
         use_bv_sorts = (uu___103_14289.use_bv_sorts);
         qtbl_name_and_index = (uu___103_14289.qtbl_name_and_index);
         normalized_eff_names = (uu___103_14289.normalized_eff_names);
         proof_ns = (uu___103_14289.proof_ns);
         synth_hook = (uu___103_14289.synth_hook);
         splice = (uu___103_14289.splice);
         is_native_tactic = (uu___103_14289.is_native_tactic);
         identifier_info = (uu___103_14289.identifier_info);
         tc_hooks = (uu___103_14289.tc_hooks);
         dsenv = (uu___103_14289.dsenv);
         dep_graph = (uu___103_14289.dep_graph)
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
      let uu___104_14320 = env  in
      {
        solver = (uu___104_14320.solver);
        range = (uu___104_14320.range);
        curmodule = (uu___104_14320.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___104_14320.gamma_cache);
        modules = (uu___104_14320.modules);
        expected_typ = (uu___104_14320.expected_typ);
        sigtab = (uu___104_14320.sigtab);
        is_pattern = (uu___104_14320.is_pattern);
        instantiate_imp = (uu___104_14320.instantiate_imp);
        effects = (uu___104_14320.effects);
        generalize = (uu___104_14320.generalize);
        letrecs = (uu___104_14320.letrecs);
        top_level = (uu___104_14320.top_level);
        check_uvars = (uu___104_14320.check_uvars);
        use_eq = (uu___104_14320.use_eq);
        is_iface = (uu___104_14320.is_iface);
        admit = (uu___104_14320.admit);
        lax = (uu___104_14320.lax);
        lax_universes = (uu___104_14320.lax_universes);
        failhard = (uu___104_14320.failhard);
        nosynth = (uu___104_14320.nosynth);
        tc_term = (uu___104_14320.tc_term);
        type_of = (uu___104_14320.type_of);
        universe_of = (uu___104_14320.universe_of);
        check_type_of = (uu___104_14320.check_type_of);
        use_bv_sorts = (uu___104_14320.use_bv_sorts);
        qtbl_name_and_index = (uu___104_14320.qtbl_name_and_index);
        normalized_eff_names = (uu___104_14320.normalized_eff_names);
        proof_ns = (uu___104_14320.proof_ns);
        synth_hook = (uu___104_14320.synth_hook);
        splice = (uu___104_14320.splice);
        is_native_tactic = (uu___104_14320.is_native_tactic);
        identifier_info = (uu___104_14320.identifier_info);
        tc_hooks = (uu___104_14320.tc_hooks);
        dsenv = (uu___104_14320.dsenv);
        dep_graph = (uu___104_14320.dep_graph)
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
            (let uu___105_14365 = env  in
             {
               solver = (uu___105_14365.solver);
               range = (uu___105_14365.range);
               curmodule = (uu___105_14365.curmodule);
               gamma = rest;
               gamma_cache = (uu___105_14365.gamma_cache);
               modules = (uu___105_14365.modules);
               expected_typ = (uu___105_14365.expected_typ);
               sigtab = (uu___105_14365.sigtab);
               is_pattern = (uu___105_14365.is_pattern);
               instantiate_imp = (uu___105_14365.instantiate_imp);
               effects = (uu___105_14365.effects);
               generalize = (uu___105_14365.generalize);
               letrecs = (uu___105_14365.letrecs);
               top_level = (uu___105_14365.top_level);
               check_uvars = (uu___105_14365.check_uvars);
               use_eq = (uu___105_14365.use_eq);
               is_iface = (uu___105_14365.is_iface);
               admit = (uu___105_14365.admit);
               lax = (uu___105_14365.lax);
               lax_universes = (uu___105_14365.lax_universes);
               failhard = (uu___105_14365.failhard);
               nosynth = (uu___105_14365.nosynth);
               tc_term = (uu___105_14365.tc_term);
               type_of = (uu___105_14365.type_of);
               universe_of = (uu___105_14365.universe_of);
               check_type_of = (uu___105_14365.check_type_of);
               use_bv_sorts = (uu___105_14365.use_bv_sorts);
               qtbl_name_and_index = (uu___105_14365.qtbl_name_and_index);
               normalized_eff_names = (uu___105_14365.normalized_eff_names);
               proof_ns = (uu___105_14365.proof_ns);
               synth_hook = (uu___105_14365.synth_hook);
               splice = (uu___105_14365.splice);
               is_native_tactic = (uu___105_14365.is_native_tactic);
               identifier_info = (uu___105_14365.identifier_info);
               tc_hooks = (uu___105_14365.tc_hooks);
               dsenv = (uu___105_14365.dsenv);
               dep_graph = (uu___105_14365.dep_graph)
             }))
    | uu____14366 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____14388  ->
             match uu____14388 with | (x,uu____14394) -> push_bv env1 x) env
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
            let uu___106_14422 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_14422.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_14422.FStar_Syntax_Syntax.index);
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
      (let uu___107_14452 = env  in
       {
         solver = (uu___107_14452.solver);
         range = (uu___107_14452.range);
         curmodule = (uu___107_14452.curmodule);
         gamma = [];
         gamma_cache = (uu___107_14452.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___107_14452.sigtab);
         is_pattern = (uu___107_14452.is_pattern);
         instantiate_imp = (uu___107_14452.instantiate_imp);
         effects = (uu___107_14452.effects);
         generalize = (uu___107_14452.generalize);
         letrecs = (uu___107_14452.letrecs);
         top_level = (uu___107_14452.top_level);
         check_uvars = (uu___107_14452.check_uvars);
         use_eq = (uu___107_14452.use_eq);
         is_iface = (uu___107_14452.is_iface);
         admit = (uu___107_14452.admit);
         lax = (uu___107_14452.lax);
         lax_universes = (uu___107_14452.lax_universes);
         failhard = (uu___107_14452.failhard);
         nosynth = (uu___107_14452.nosynth);
         tc_term = (uu___107_14452.tc_term);
         type_of = (uu___107_14452.type_of);
         universe_of = (uu___107_14452.universe_of);
         check_type_of = (uu___107_14452.check_type_of);
         use_bv_sorts = (uu___107_14452.use_bv_sorts);
         qtbl_name_and_index = (uu___107_14452.qtbl_name_and_index);
         normalized_eff_names = (uu___107_14452.normalized_eff_names);
         proof_ns = (uu___107_14452.proof_ns);
         synth_hook = (uu___107_14452.synth_hook);
         splice = (uu___107_14452.splice);
         is_native_tactic = (uu___107_14452.is_native_tactic);
         identifier_info = (uu___107_14452.identifier_info);
         tc_hooks = (uu___107_14452.tc_hooks);
         dsenv = (uu___107_14452.dsenv);
         dep_graph = (uu___107_14452.dep_graph)
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
        let uu____14484 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____14484 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____14512 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____14512)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___108_14525 = env  in
      {
        solver = (uu___108_14525.solver);
        range = (uu___108_14525.range);
        curmodule = (uu___108_14525.curmodule);
        gamma = (uu___108_14525.gamma);
        gamma_cache = (uu___108_14525.gamma_cache);
        modules = (uu___108_14525.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___108_14525.sigtab);
        is_pattern = (uu___108_14525.is_pattern);
        instantiate_imp = (uu___108_14525.instantiate_imp);
        effects = (uu___108_14525.effects);
        generalize = (uu___108_14525.generalize);
        letrecs = (uu___108_14525.letrecs);
        top_level = (uu___108_14525.top_level);
        check_uvars = (uu___108_14525.check_uvars);
        use_eq = false;
        is_iface = (uu___108_14525.is_iface);
        admit = (uu___108_14525.admit);
        lax = (uu___108_14525.lax);
        lax_universes = (uu___108_14525.lax_universes);
        failhard = (uu___108_14525.failhard);
        nosynth = (uu___108_14525.nosynth);
        tc_term = (uu___108_14525.tc_term);
        type_of = (uu___108_14525.type_of);
        universe_of = (uu___108_14525.universe_of);
        check_type_of = (uu___108_14525.check_type_of);
        use_bv_sorts = (uu___108_14525.use_bv_sorts);
        qtbl_name_and_index = (uu___108_14525.qtbl_name_and_index);
        normalized_eff_names = (uu___108_14525.normalized_eff_names);
        proof_ns = (uu___108_14525.proof_ns);
        synth_hook = (uu___108_14525.synth_hook);
        splice = (uu___108_14525.splice);
        is_native_tactic = (uu___108_14525.is_native_tactic);
        identifier_info = (uu___108_14525.identifier_info);
        tc_hooks = (uu___108_14525.tc_hooks);
        dsenv = (uu___108_14525.dsenv);
        dep_graph = (uu___108_14525.dep_graph)
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
    let uu____14549 = expected_typ env_  in
    ((let uu___109_14555 = env_  in
      {
        solver = (uu___109_14555.solver);
        range = (uu___109_14555.range);
        curmodule = (uu___109_14555.curmodule);
        gamma = (uu___109_14555.gamma);
        gamma_cache = (uu___109_14555.gamma_cache);
        modules = (uu___109_14555.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___109_14555.sigtab);
        is_pattern = (uu___109_14555.is_pattern);
        instantiate_imp = (uu___109_14555.instantiate_imp);
        effects = (uu___109_14555.effects);
        generalize = (uu___109_14555.generalize);
        letrecs = (uu___109_14555.letrecs);
        top_level = (uu___109_14555.top_level);
        check_uvars = (uu___109_14555.check_uvars);
        use_eq = false;
        is_iface = (uu___109_14555.is_iface);
        admit = (uu___109_14555.admit);
        lax = (uu___109_14555.lax);
        lax_universes = (uu___109_14555.lax_universes);
        failhard = (uu___109_14555.failhard);
        nosynth = (uu___109_14555.nosynth);
        tc_term = (uu___109_14555.tc_term);
        type_of = (uu___109_14555.type_of);
        universe_of = (uu___109_14555.universe_of);
        check_type_of = (uu___109_14555.check_type_of);
        use_bv_sorts = (uu___109_14555.use_bv_sorts);
        qtbl_name_and_index = (uu___109_14555.qtbl_name_and_index);
        normalized_eff_names = (uu___109_14555.normalized_eff_names);
        proof_ns = (uu___109_14555.proof_ns);
        synth_hook = (uu___109_14555.synth_hook);
        splice = (uu___109_14555.splice);
        is_native_tactic = (uu___109_14555.is_native_tactic);
        identifier_info = (uu___109_14555.identifier_info);
        tc_hooks = (uu___109_14555.tc_hooks);
        dsenv = (uu___109_14555.dsenv);
        dep_graph = (uu___109_14555.dep_graph)
      }), uu____14549)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____14561 =
      let uu____14564 = FStar_Ident.id_of_text ""  in [uu____14564]  in
    FStar_Ident.lid_of_ids uu____14561  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____14570 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14570
        then
          let uu____14573 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___83_14583  ->
                    match uu___83_14583 with
                    | Binding_sig (uu____14586,se) -> [se]
                    | uu____14592 -> []))
             in
          FStar_All.pipe_right uu____14573 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___110_14599 = env  in
       {
         solver = (uu___110_14599.solver);
         range = (uu___110_14599.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___110_14599.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___110_14599.expected_typ);
         sigtab = (uu___110_14599.sigtab);
         is_pattern = (uu___110_14599.is_pattern);
         instantiate_imp = (uu___110_14599.instantiate_imp);
         effects = (uu___110_14599.effects);
         generalize = (uu___110_14599.generalize);
         letrecs = (uu___110_14599.letrecs);
         top_level = (uu___110_14599.top_level);
         check_uvars = (uu___110_14599.check_uvars);
         use_eq = (uu___110_14599.use_eq);
         is_iface = (uu___110_14599.is_iface);
         admit = (uu___110_14599.admit);
         lax = (uu___110_14599.lax);
         lax_universes = (uu___110_14599.lax_universes);
         failhard = (uu___110_14599.failhard);
         nosynth = (uu___110_14599.nosynth);
         tc_term = (uu___110_14599.tc_term);
         type_of = (uu___110_14599.type_of);
         universe_of = (uu___110_14599.universe_of);
         check_type_of = (uu___110_14599.check_type_of);
         use_bv_sorts = (uu___110_14599.use_bv_sorts);
         qtbl_name_and_index = (uu___110_14599.qtbl_name_and_index);
         normalized_eff_names = (uu___110_14599.normalized_eff_names);
         proof_ns = (uu___110_14599.proof_ns);
         synth_hook = (uu___110_14599.synth_hook);
         splice = (uu___110_14599.splice);
         is_native_tactic = (uu___110_14599.is_native_tactic);
         identifier_info = (uu___110_14599.identifier_info);
         tc_hooks = (uu___110_14599.tc_hooks);
         dsenv = (uu___110_14599.dsenv);
         dep_graph = (uu___110_14599.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14680)::tl1 -> aux out tl1
      | (Binding_lid (uu____14684,(uu____14685,t)))::tl1 ->
          let uu____14700 =
            let uu____14707 = FStar_Syntax_Free.uvars t  in
            ext out uu____14707  in
          aux uu____14700 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14714;
            FStar_Syntax_Syntax.index = uu____14715;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14722 =
            let uu____14729 = FStar_Syntax_Free.uvars t  in
            ext out uu____14729  in
          aux uu____14722 tl1
      | (Binding_sig uu____14736)::uu____14737 -> out
      | (Binding_sig_inst uu____14746)::uu____14747 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14802)::tl1 -> aux out tl1
      | (Binding_univ uu____14814)::tl1 -> aux out tl1
      | (Binding_lid (uu____14818,(uu____14819,t)))::tl1 ->
          let uu____14834 =
            let uu____14837 = FStar_Syntax_Free.univs t  in
            ext out uu____14837  in
          aux uu____14834 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14840;
            FStar_Syntax_Syntax.index = uu____14841;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14848 =
            let uu____14851 = FStar_Syntax_Free.univs t  in
            ext out uu____14851  in
          aux uu____14848 tl1
      | (Binding_sig uu____14854)::uu____14855 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14908)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14924 = FStar_Util.set_add uname out  in
          aux uu____14924 tl1
      | (Binding_lid (uu____14927,(uu____14928,t)))::tl1 ->
          let uu____14943 =
            let uu____14946 = FStar_Syntax_Free.univnames t  in
            ext out uu____14946  in
          aux uu____14943 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14949;
            FStar_Syntax_Syntax.index = uu____14950;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14957 =
            let uu____14960 = FStar_Syntax_Free.univnames t  in
            ext out uu____14960  in
          aux uu____14957 tl1
      | (Binding_sig uu____14963)::uu____14964 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___84_14988  ->
            match uu___84_14988 with
            | Binding_var x -> [x]
            | Binding_lid uu____14992 -> []
            | Binding_sig uu____14997 -> []
            | Binding_univ uu____15004 -> []
            | Binding_sig_inst uu____15005 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____15021 =
      let uu____15024 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____15024
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____15021 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____15046 =
      let uu____15047 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___85_15057  ->
                match uu___85_15057 with
                | Binding_var x ->
                    let uu____15059 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____15059
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____15062) ->
                    let uu____15063 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____15063
                | Binding_sig (ls,uu____15065) ->
                    let uu____15070 =
                      let uu____15071 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____15071
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____15070
                | Binding_sig_inst (ls,uu____15081,uu____15082) ->
                    let uu____15087 =
                      let uu____15088 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____15088
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____15087))
         in
      FStar_All.pipe_right uu____15047 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____15046 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____15105 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____15105
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____15133  ->
                 fun uu____15134  ->
                   match (uu____15133, uu____15134) with
                   | ((b1,uu____15152),(b2,uu____15154)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___86_15196  ->
    match uu___86_15196 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____15197 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___87_15215  ->
             match uu___87_15215 with
             | Binding_sig (lids,uu____15221) -> FStar_List.append lids keys
             | uu____15226 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____15232  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____15266) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____15285,uu____15286) -> false  in
      let uu____15295 =
        FStar_List.tryFind
          (fun uu____15313  ->
             match uu____15313 with | (p,uu____15321) -> list_prefix p path)
          env.proof_ns
         in
      match uu____15295 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____15332,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15350 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____15350
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___111_15362 = e  in
        {
          solver = (uu___111_15362.solver);
          range = (uu___111_15362.range);
          curmodule = (uu___111_15362.curmodule);
          gamma = (uu___111_15362.gamma);
          gamma_cache = (uu___111_15362.gamma_cache);
          modules = (uu___111_15362.modules);
          expected_typ = (uu___111_15362.expected_typ);
          sigtab = (uu___111_15362.sigtab);
          is_pattern = (uu___111_15362.is_pattern);
          instantiate_imp = (uu___111_15362.instantiate_imp);
          effects = (uu___111_15362.effects);
          generalize = (uu___111_15362.generalize);
          letrecs = (uu___111_15362.letrecs);
          top_level = (uu___111_15362.top_level);
          check_uvars = (uu___111_15362.check_uvars);
          use_eq = (uu___111_15362.use_eq);
          is_iface = (uu___111_15362.is_iface);
          admit = (uu___111_15362.admit);
          lax = (uu___111_15362.lax);
          lax_universes = (uu___111_15362.lax_universes);
          failhard = (uu___111_15362.failhard);
          nosynth = (uu___111_15362.nosynth);
          tc_term = (uu___111_15362.tc_term);
          type_of = (uu___111_15362.type_of);
          universe_of = (uu___111_15362.universe_of);
          check_type_of = (uu___111_15362.check_type_of);
          use_bv_sorts = (uu___111_15362.use_bv_sorts);
          qtbl_name_and_index = (uu___111_15362.qtbl_name_and_index);
          normalized_eff_names = (uu___111_15362.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___111_15362.synth_hook);
          splice = (uu___111_15362.splice);
          is_native_tactic = (uu___111_15362.is_native_tactic);
          identifier_info = (uu___111_15362.identifier_info);
          tc_hooks = (uu___111_15362.tc_hooks);
          dsenv = (uu___111_15362.dsenv);
          dep_graph = (uu___111_15362.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___112_15388 = e  in
      {
        solver = (uu___112_15388.solver);
        range = (uu___112_15388.range);
        curmodule = (uu___112_15388.curmodule);
        gamma = (uu___112_15388.gamma);
        gamma_cache = (uu___112_15388.gamma_cache);
        modules = (uu___112_15388.modules);
        expected_typ = (uu___112_15388.expected_typ);
        sigtab = (uu___112_15388.sigtab);
        is_pattern = (uu___112_15388.is_pattern);
        instantiate_imp = (uu___112_15388.instantiate_imp);
        effects = (uu___112_15388.effects);
        generalize = (uu___112_15388.generalize);
        letrecs = (uu___112_15388.letrecs);
        top_level = (uu___112_15388.top_level);
        check_uvars = (uu___112_15388.check_uvars);
        use_eq = (uu___112_15388.use_eq);
        is_iface = (uu___112_15388.is_iface);
        admit = (uu___112_15388.admit);
        lax = (uu___112_15388.lax);
        lax_universes = (uu___112_15388.lax_universes);
        failhard = (uu___112_15388.failhard);
        nosynth = (uu___112_15388.nosynth);
        tc_term = (uu___112_15388.tc_term);
        type_of = (uu___112_15388.type_of);
        universe_of = (uu___112_15388.universe_of);
        check_type_of = (uu___112_15388.check_type_of);
        use_bv_sorts = (uu___112_15388.use_bv_sorts);
        qtbl_name_and_index = (uu___112_15388.qtbl_name_and_index);
        normalized_eff_names = (uu___112_15388.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___112_15388.synth_hook);
        splice = (uu___112_15388.splice);
        is_native_tactic = (uu___112_15388.is_native_tactic);
        identifier_info = (uu___112_15388.identifier_info);
        tc_hooks = (uu___112_15388.tc_hooks);
        dsenv = (uu___112_15388.dsenv);
        dep_graph = (uu___112_15388.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____15399 = FStar_Syntax_Free.names t  in
      let uu____15402 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____15399 uu____15402
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____15419 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____15419
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____15425 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____15425
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____15440 =
      match uu____15440 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____15456 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____15456)
       in
    let uu____15458 =
      let uu____15461 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____15461 FStar_List.rev  in
    FStar_All.pipe_right uu____15458 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____15478  -> ());
    push = (fun uu____15480  -> ());
    pop = (fun uu____15482  -> ());
    encode_modul = (fun uu____15485  -> fun uu____15486  -> ());
    encode_sig = (fun uu____15489  -> fun uu____15490  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____15496 =
             let uu____15503 = FStar_Options.peek ()  in (e, g, uu____15503)
              in
           [uu____15496]);
    solve = (fun uu____15519  -> fun uu____15520  -> fun uu____15521  -> ());
    finish = (fun uu____15527  -> ());
    refresh = (fun uu____15529  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___113_15533 = en  in
    let uu____15534 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____15537 = FStar_Util.smap_copy en.sigtab  in
    let uu____15540 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___113_15533.solver);
      range = (uu___113_15533.range);
      curmodule = (uu___113_15533.curmodule);
      gamma = (uu___113_15533.gamma);
      gamma_cache = uu____15534;
      modules = (uu___113_15533.modules);
      expected_typ = (uu___113_15533.expected_typ);
      sigtab = uu____15537;
      is_pattern = (uu___113_15533.is_pattern);
      instantiate_imp = (uu___113_15533.instantiate_imp);
      effects = (uu___113_15533.effects);
      generalize = (uu___113_15533.generalize);
      letrecs = (uu___113_15533.letrecs);
      top_level = (uu___113_15533.top_level);
      check_uvars = (uu___113_15533.check_uvars);
      use_eq = (uu___113_15533.use_eq);
      is_iface = (uu___113_15533.is_iface);
      admit = (uu___113_15533.admit);
      lax = (uu___113_15533.lax);
      lax_universes = (uu___113_15533.lax_universes);
      failhard = (uu___113_15533.failhard);
      nosynth = (uu___113_15533.nosynth);
      tc_term = (uu___113_15533.tc_term);
      type_of = (uu___113_15533.type_of);
      universe_of = (uu___113_15533.universe_of);
      check_type_of = (uu___113_15533.check_type_of);
      use_bv_sorts = (uu___113_15533.use_bv_sorts);
      qtbl_name_and_index = (uu___113_15533.qtbl_name_and_index);
      normalized_eff_names = (uu___113_15533.normalized_eff_names);
      proof_ns = (uu___113_15533.proof_ns);
      synth_hook = (uu___113_15533.synth_hook);
      splice = (uu___113_15533.splice);
      is_native_tactic = (uu___113_15533.is_native_tactic);
      identifier_info = (uu___113_15533.identifier_info);
      tc_hooks = (uu___113_15533.tc_hooks);
      dsenv = uu____15540;
      dep_graph = (uu___113_15533.dep_graph)
    }
  