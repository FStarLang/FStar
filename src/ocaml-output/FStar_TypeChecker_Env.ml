open Prims
type sig_binding =
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2[@@deriving show]
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac [@@deriving show]
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____17 -> false
  
let (uu___is_Inlining : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____23 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____29 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____36 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
let (uu___is_UnfoldTac : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____49 -> false
  
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
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
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
    (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
      FStar_Range.range,Prims.bool) FStar_Pervasives_Native.tuple5 Prims.list
    }[@@deriving show]
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }[@@deriving show]
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        dep_graph = __fname__dep_graph;_} -> __fname__gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
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
    (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
      FStar_Range.range,Prims.bool) FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type implicits =
  (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
    FStar_Range.range,Prims.bool) FStar_Pervasives_Native.tuple5 Prims.list
[@@deriving show]
let (rename_gamma :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binding Prims.list ->
      FStar_Syntax_Syntax.binding Prims.list)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___74_7551  ->
              match uu___74_7551 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____7554 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____7554  in
                  let uu____7555 =
                    let uu____7556 = FStar_Syntax_Subst.compress y  in
                    uu____7556.FStar_Syntax_Syntax.n  in
                  (match uu____7555 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____7560 =
                         let uu___88_7561 = y1  in
                         let uu____7562 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___88_7561.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___88_7561.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____7562
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____7560
                   | uu____7565 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___89_7577 = env  in
      let uu____7578 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___89_7577.solver);
        range = (uu___89_7577.range);
        curmodule = (uu___89_7577.curmodule);
        gamma = uu____7578;
        gamma_sig = (uu___89_7577.gamma_sig);
        gamma_cache = (uu___89_7577.gamma_cache);
        modules = (uu___89_7577.modules);
        expected_typ = (uu___89_7577.expected_typ);
        sigtab = (uu___89_7577.sigtab);
        is_pattern = (uu___89_7577.is_pattern);
        instantiate_imp = (uu___89_7577.instantiate_imp);
        effects = (uu___89_7577.effects);
        generalize = (uu___89_7577.generalize);
        letrecs = (uu___89_7577.letrecs);
        top_level = (uu___89_7577.top_level);
        check_uvars = (uu___89_7577.check_uvars);
        use_eq = (uu___89_7577.use_eq);
        is_iface = (uu___89_7577.is_iface);
        admit = (uu___89_7577.admit);
        lax = (uu___89_7577.lax);
        lax_universes = (uu___89_7577.lax_universes);
        failhard = (uu___89_7577.failhard);
        nosynth = (uu___89_7577.nosynth);
        tc_term = (uu___89_7577.tc_term);
        type_of = (uu___89_7577.type_of);
        universe_of = (uu___89_7577.universe_of);
        check_type_of = (uu___89_7577.check_type_of);
        use_bv_sorts = (uu___89_7577.use_bv_sorts);
        qtbl_name_and_index = (uu___89_7577.qtbl_name_and_index);
        normalized_eff_names = (uu___89_7577.normalized_eff_names);
        proof_ns = (uu___89_7577.proof_ns);
        synth_hook = (uu___89_7577.synth_hook);
        splice = (uu___89_7577.splice);
        is_native_tactic = (uu___89_7577.is_native_tactic);
        identifier_info = (uu___89_7577.identifier_info);
        tc_hooks = (uu___89_7577.tc_hooks);
        dsenv = (uu___89_7577.dsenv);
        dep_graph = (uu___89_7577.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____7585  -> fun uu____7586  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___90_7606 = env  in
      {
        solver = (uu___90_7606.solver);
        range = (uu___90_7606.range);
        curmodule = (uu___90_7606.curmodule);
        gamma = (uu___90_7606.gamma);
        gamma_sig = (uu___90_7606.gamma_sig);
        gamma_cache = (uu___90_7606.gamma_cache);
        modules = (uu___90_7606.modules);
        expected_typ = (uu___90_7606.expected_typ);
        sigtab = (uu___90_7606.sigtab);
        is_pattern = (uu___90_7606.is_pattern);
        instantiate_imp = (uu___90_7606.instantiate_imp);
        effects = (uu___90_7606.effects);
        generalize = (uu___90_7606.generalize);
        letrecs = (uu___90_7606.letrecs);
        top_level = (uu___90_7606.top_level);
        check_uvars = (uu___90_7606.check_uvars);
        use_eq = (uu___90_7606.use_eq);
        is_iface = (uu___90_7606.is_iface);
        admit = (uu___90_7606.admit);
        lax = (uu___90_7606.lax);
        lax_universes = (uu___90_7606.lax_universes);
        failhard = (uu___90_7606.failhard);
        nosynth = (uu___90_7606.nosynth);
        tc_term = (uu___90_7606.tc_term);
        type_of = (uu___90_7606.type_of);
        universe_of = (uu___90_7606.universe_of);
        check_type_of = (uu___90_7606.check_type_of);
        use_bv_sorts = (uu___90_7606.use_bv_sorts);
        qtbl_name_and_index = (uu___90_7606.qtbl_name_and_index);
        normalized_eff_names = (uu___90_7606.normalized_eff_names);
        proof_ns = (uu___90_7606.proof_ns);
        synth_hook = (uu___90_7606.synth_hook);
        splice = (uu___90_7606.splice);
        is_native_tactic = (uu___90_7606.is_native_tactic);
        identifier_info = (uu___90_7606.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___90_7606.dsenv);
        dep_graph = (uu___90_7606.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___91_7617 = e  in
      {
        solver = (uu___91_7617.solver);
        range = (uu___91_7617.range);
        curmodule = (uu___91_7617.curmodule);
        gamma = (uu___91_7617.gamma);
        gamma_sig = (uu___91_7617.gamma_sig);
        gamma_cache = (uu___91_7617.gamma_cache);
        modules = (uu___91_7617.modules);
        expected_typ = (uu___91_7617.expected_typ);
        sigtab = (uu___91_7617.sigtab);
        is_pattern = (uu___91_7617.is_pattern);
        instantiate_imp = (uu___91_7617.instantiate_imp);
        effects = (uu___91_7617.effects);
        generalize = (uu___91_7617.generalize);
        letrecs = (uu___91_7617.letrecs);
        top_level = (uu___91_7617.top_level);
        check_uvars = (uu___91_7617.check_uvars);
        use_eq = (uu___91_7617.use_eq);
        is_iface = (uu___91_7617.is_iface);
        admit = (uu___91_7617.admit);
        lax = (uu___91_7617.lax);
        lax_universes = (uu___91_7617.lax_universes);
        failhard = (uu___91_7617.failhard);
        nosynth = (uu___91_7617.nosynth);
        tc_term = (uu___91_7617.tc_term);
        type_of = (uu___91_7617.type_of);
        universe_of = (uu___91_7617.universe_of);
        check_type_of = (uu___91_7617.check_type_of);
        use_bv_sorts = (uu___91_7617.use_bv_sorts);
        qtbl_name_and_index = (uu___91_7617.qtbl_name_and_index);
        normalized_eff_names = (uu___91_7617.normalized_eff_names);
        proof_ns = (uu___91_7617.proof_ns);
        synth_hook = (uu___91_7617.synth_hook);
        splice = (uu___91_7617.splice);
        is_native_tactic = (uu___91_7617.is_native_tactic);
        identifier_info = (uu___91_7617.identifier_info);
        tc_hooks = (uu___91_7617.tc_hooks);
        dsenv = (uu___91_7617.dsenv);
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
      | (NoDelta ,uu____7640) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____7641,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____7642,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____7643 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____7652 . unit -> 'Auu____7652 FStar_Util.smap =
  fun uu____7659  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____7664 . unit -> 'Auu____7664 FStar_Util.smap =
  fun uu____7671  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____7781 = new_gamma_cache ()  in
                let uu____7784 = new_sigtab ()  in
                let uu____7787 =
                  let uu____7800 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____7800, FStar_Pervasives_Native.None)  in
                let uu____7815 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____7818 = FStar_Options.using_facts_from ()  in
                let uu____7819 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____7822 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____7781;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____7784;
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
                  qtbl_name_and_index = uu____7787;
                  normalized_eff_names = uu____7815;
                  proof_ns = uu____7818;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____7858  -> false);
                  identifier_info = uu____7819;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____7822;
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
  fun uu____7949  ->
    let uu____7950 = FStar_ST.op_Bang query_indices  in
    match uu____7950 with
    | [] -> failwith "Empty query indices!"
    | uu____8004 ->
        let uu____8013 =
          let uu____8022 =
            let uu____8029 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8029  in
          let uu____8083 = FStar_ST.op_Bang query_indices  in uu____8022 ::
            uu____8083
           in
        FStar_ST.op_Colon_Equals query_indices uu____8013
  
let (pop_query_indices : unit -> unit) =
  fun uu____8180  ->
    let uu____8181 = FStar_ST.op_Bang query_indices  in
    match uu____8181 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8304  ->
    match uu____8304 with
    | (l,n1) ->
        let uu____8311 = FStar_ST.op_Bang query_indices  in
        (match uu____8311 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____8430 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____8449  ->
    let uu____8450 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____8450
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____8527 =
       let uu____8530 = FStar_ST.op_Bang stack  in env :: uu____8530  in
     FStar_ST.op_Colon_Equals stack uu____8527);
    (let uu___92_8587 = env  in
     let uu____8588 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____8591 = FStar_Util.smap_copy (sigtab env)  in
     let uu____8594 =
       let uu____8607 =
         let uu____8610 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____8610  in
       let uu____8635 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____8607, uu____8635)  in
     let uu____8676 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____8679 =
       let uu____8682 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____8682  in
     {
       solver = (uu___92_8587.solver);
       range = (uu___92_8587.range);
       curmodule = (uu___92_8587.curmodule);
       gamma = (uu___92_8587.gamma);
       gamma_sig = (uu___92_8587.gamma_sig);
       gamma_cache = uu____8588;
       modules = (uu___92_8587.modules);
       expected_typ = (uu___92_8587.expected_typ);
       sigtab = uu____8591;
       is_pattern = (uu___92_8587.is_pattern);
       instantiate_imp = (uu___92_8587.instantiate_imp);
       effects = (uu___92_8587.effects);
       generalize = (uu___92_8587.generalize);
       letrecs = (uu___92_8587.letrecs);
       top_level = (uu___92_8587.top_level);
       check_uvars = (uu___92_8587.check_uvars);
       use_eq = (uu___92_8587.use_eq);
       is_iface = (uu___92_8587.is_iface);
       admit = (uu___92_8587.admit);
       lax = (uu___92_8587.lax);
       lax_universes = (uu___92_8587.lax_universes);
       failhard = (uu___92_8587.failhard);
       nosynth = (uu___92_8587.nosynth);
       tc_term = (uu___92_8587.tc_term);
       type_of = (uu___92_8587.type_of);
       universe_of = (uu___92_8587.universe_of);
       check_type_of = (uu___92_8587.check_type_of);
       use_bv_sorts = (uu___92_8587.use_bv_sorts);
       qtbl_name_and_index = uu____8594;
       normalized_eff_names = uu____8676;
       proof_ns = (uu___92_8587.proof_ns);
       synth_hook = (uu___92_8587.synth_hook);
       splice = (uu___92_8587.splice);
       is_native_tactic = (uu___92_8587.is_native_tactic);
       identifier_info = uu____8679;
       tc_hooks = (uu___92_8587.tc_hooks);
       dsenv = (uu___92_8587.dsenv);
       dep_graph = (uu___92_8587.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____8732  ->
    let uu____8733 = FStar_ST.op_Bang stack  in
    match uu____8733 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____8795 -> failwith "Impossible: Too many pops"
  
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
    | (uu____8834,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____8866 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____8892  ->
                  match uu____8892 with
                  | (m,uu____8898) -> FStar_Ident.lid_equals l m))
           in
        (match uu____8866 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___93_8906 = env  in
               {
                 solver = (uu___93_8906.solver);
                 range = (uu___93_8906.range);
                 curmodule = (uu___93_8906.curmodule);
                 gamma = (uu___93_8906.gamma);
                 gamma_sig = (uu___93_8906.gamma_sig);
                 gamma_cache = (uu___93_8906.gamma_cache);
                 modules = (uu___93_8906.modules);
                 expected_typ = (uu___93_8906.expected_typ);
                 sigtab = (uu___93_8906.sigtab);
                 is_pattern = (uu___93_8906.is_pattern);
                 instantiate_imp = (uu___93_8906.instantiate_imp);
                 effects = (uu___93_8906.effects);
                 generalize = (uu___93_8906.generalize);
                 letrecs = (uu___93_8906.letrecs);
                 top_level = (uu___93_8906.top_level);
                 check_uvars = (uu___93_8906.check_uvars);
                 use_eq = (uu___93_8906.use_eq);
                 is_iface = (uu___93_8906.is_iface);
                 admit = (uu___93_8906.admit);
                 lax = (uu___93_8906.lax);
                 lax_universes = (uu___93_8906.lax_universes);
                 failhard = (uu___93_8906.failhard);
                 nosynth = (uu___93_8906.nosynth);
                 tc_term = (uu___93_8906.tc_term);
                 type_of = (uu___93_8906.type_of);
                 universe_of = (uu___93_8906.universe_of);
                 check_type_of = (uu___93_8906.check_type_of);
                 use_bv_sorts = (uu___93_8906.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___93_8906.normalized_eff_names);
                 proof_ns = (uu___93_8906.proof_ns);
                 synth_hook = (uu___93_8906.synth_hook);
                 splice = (uu___93_8906.splice);
                 is_native_tactic = (uu___93_8906.is_native_tactic);
                 identifier_info = (uu___93_8906.identifier_info);
                 tc_hooks = (uu___93_8906.tc_hooks);
                 dsenv = (uu___93_8906.dsenv);
                 dep_graph = (uu___93_8906.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____8919,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___94_8928 = env  in
               {
                 solver = (uu___94_8928.solver);
                 range = (uu___94_8928.range);
                 curmodule = (uu___94_8928.curmodule);
                 gamma = (uu___94_8928.gamma);
                 gamma_sig = (uu___94_8928.gamma_sig);
                 gamma_cache = (uu___94_8928.gamma_cache);
                 modules = (uu___94_8928.modules);
                 expected_typ = (uu___94_8928.expected_typ);
                 sigtab = (uu___94_8928.sigtab);
                 is_pattern = (uu___94_8928.is_pattern);
                 instantiate_imp = (uu___94_8928.instantiate_imp);
                 effects = (uu___94_8928.effects);
                 generalize = (uu___94_8928.generalize);
                 letrecs = (uu___94_8928.letrecs);
                 top_level = (uu___94_8928.top_level);
                 check_uvars = (uu___94_8928.check_uvars);
                 use_eq = (uu___94_8928.use_eq);
                 is_iface = (uu___94_8928.is_iface);
                 admit = (uu___94_8928.admit);
                 lax = (uu___94_8928.lax);
                 lax_universes = (uu___94_8928.lax_universes);
                 failhard = (uu___94_8928.failhard);
                 nosynth = (uu___94_8928.nosynth);
                 tc_term = (uu___94_8928.tc_term);
                 type_of = (uu___94_8928.type_of);
                 universe_of = (uu___94_8928.universe_of);
                 check_type_of = (uu___94_8928.check_type_of);
                 use_bv_sorts = (uu___94_8928.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___94_8928.normalized_eff_names);
                 proof_ns = (uu___94_8928.proof_ns);
                 synth_hook = (uu___94_8928.synth_hook);
                 splice = (uu___94_8928.splice);
                 is_native_tactic = (uu___94_8928.is_native_tactic);
                 identifier_info = (uu___94_8928.identifier_info);
                 tc_hooks = (uu___94_8928.tc_hooks);
                 dsenv = (uu___94_8928.dsenv);
                 dep_graph = (uu___94_8928.dep_graph)
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
        (let uu___95_8962 = e  in
         {
           solver = (uu___95_8962.solver);
           range = r;
           curmodule = (uu___95_8962.curmodule);
           gamma = (uu___95_8962.gamma);
           gamma_sig = (uu___95_8962.gamma_sig);
           gamma_cache = (uu___95_8962.gamma_cache);
           modules = (uu___95_8962.modules);
           expected_typ = (uu___95_8962.expected_typ);
           sigtab = (uu___95_8962.sigtab);
           is_pattern = (uu___95_8962.is_pattern);
           instantiate_imp = (uu___95_8962.instantiate_imp);
           effects = (uu___95_8962.effects);
           generalize = (uu___95_8962.generalize);
           letrecs = (uu___95_8962.letrecs);
           top_level = (uu___95_8962.top_level);
           check_uvars = (uu___95_8962.check_uvars);
           use_eq = (uu___95_8962.use_eq);
           is_iface = (uu___95_8962.is_iface);
           admit = (uu___95_8962.admit);
           lax = (uu___95_8962.lax);
           lax_universes = (uu___95_8962.lax_universes);
           failhard = (uu___95_8962.failhard);
           nosynth = (uu___95_8962.nosynth);
           tc_term = (uu___95_8962.tc_term);
           type_of = (uu___95_8962.type_of);
           universe_of = (uu___95_8962.universe_of);
           check_type_of = (uu___95_8962.check_type_of);
           use_bv_sorts = (uu___95_8962.use_bv_sorts);
           qtbl_name_and_index = (uu___95_8962.qtbl_name_and_index);
           normalized_eff_names = (uu___95_8962.normalized_eff_names);
           proof_ns = (uu___95_8962.proof_ns);
           synth_hook = (uu___95_8962.synth_hook);
           splice = (uu___95_8962.splice);
           is_native_tactic = (uu___95_8962.is_native_tactic);
           identifier_info = (uu___95_8962.identifier_info);
           tc_hooks = (uu___95_8962.tc_hooks);
           dsenv = (uu___95_8962.dsenv);
           dep_graph = (uu___95_8962.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____8978 =
        let uu____8979 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____8979 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____8978
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____9041 =
          let uu____9042 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____9042 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9041
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____9104 =
          let uu____9105 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____9105 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9104
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____9167 =
        let uu____9168 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____9168 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9167
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___96_9237 = env  in
      {
        solver = (uu___96_9237.solver);
        range = (uu___96_9237.range);
        curmodule = lid;
        gamma = (uu___96_9237.gamma);
        gamma_sig = (uu___96_9237.gamma_sig);
        gamma_cache = (uu___96_9237.gamma_cache);
        modules = (uu___96_9237.modules);
        expected_typ = (uu___96_9237.expected_typ);
        sigtab = (uu___96_9237.sigtab);
        is_pattern = (uu___96_9237.is_pattern);
        instantiate_imp = (uu___96_9237.instantiate_imp);
        effects = (uu___96_9237.effects);
        generalize = (uu___96_9237.generalize);
        letrecs = (uu___96_9237.letrecs);
        top_level = (uu___96_9237.top_level);
        check_uvars = (uu___96_9237.check_uvars);
        use_eq = (uu___96_9237.use_eq);
        is_iface = (uu___96_9237.is_iface);
        admit = (uu___96_9237.admit);
        lax = (uu___96_9237.lax);
        lax_universes = (uu___96_9237.lax_universes);
        failhard = (uu___96_9237.failhard);
        nosynth = (uu___96_9237.nosynth);
        tc_term = (uu___96_9237.tc_term);
        type_of = (uu___96_9237.type_of);
        universe_of = (uu___96_9237.universe_of);
        check_type_of = (uu___96_9237.check_type_of);
        use_bv_sorts = (uu___96_9237.use_bv_sorts);
        qtbl_name_and_index = (uu___96_9237.qtbl_name_and_index);
        normalized_eff_names = (uu___96_9237.normalized_eff_names);
        proof_ns = (uu___96_9237.proof_ns);
        synth_hook = (uu___96_9237.synth_hook);
        splice = (uu___96_9237.splice);
        is_native_tactic = (uu___96_9237.is_native_tactic);
        identifier_info = (uu___96_9237.identifier_info);
        tc_hooks = (uu___96_9237.tc_hooks);
        dsenv = (uu___96_9237.dsenv);
        dep_graph = (uu___96_9237.dep_graph)
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
      let uu____9264 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____9264
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____9274 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____9274)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____9284 =
      let uu____9285 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____9285  in
    (FStar_Errors.Fatal_VariableNotFound, uu____9284)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____9290  ->
    let uu____9291 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____9291
  
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
      | ((formals,t),uu____9347) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____9381 = FStar_Syntax_Subst.subst vs t  in (us, uu____9381)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___75_9397  ->
    match uu___75_9397 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____9423  -> new_u_univ ()))
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
      let uu____9442 = inst_tscheme t  in
      match uu____9442 with
      | (us,t1) ->
          let uu____9453 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____9453)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____9473  ->
          match uu____9473 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____9492 =
                         let uu____9493 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____9494 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____9495 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____9496 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____9493 uu____9494 uu____9495 uu____9496
                          in
                       failwith uu____9492)
                    else ();
                    (let uu____9498 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____9498))
               | uu____9507 ->
                   let uu____9508 =
                     let uu____9509 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____9509
                      in
                   failwith uu____9508)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____9515 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____9521 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____9527 -> false
  
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
             | ([],uu____9569) -> Maybe
             | (uu____9576,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____9595 -> No  in
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
          let uu____9686 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____9686 with
          | FStar_Pervasives_Native.None  ->
              let uu____9709 =
                FStar_Util.find_map env.gamma
                  (fun uu___76_9753  ->
                     match uu___76_9753 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____9792 = FStar_Ident.lid_equals lid l  in
                         if uu____9792
                         then
                           let uu____9813 =
                             let uu____9832 =
                               let uu____9847 = inst_tscheme t  in
                               FStar_Util.Inl uu____9847  in
                             let uu____9862 = FStar_Ident.range_of_lid l  in
                             (uu____9832, uu____9862)  in
                           FStar_Pervasives_Native.Some uu____9813
                         else FStar_Pervasives_Native.None
                     | uu____9914 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____9709
                (fun uu____9952  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___77_9961  ->
                        match uu___77_9961 with
                        | (uu____9964,{
                                        FStar_Syntax_Syntax.sigel =
                                          FStar_Syntax_Syntax.Sig_bundle
                                          (ses,uu____9966);
                                        FStar_Syntax_Syntax.sigrng =
                                          uu____9967;
                                        FStar_Syntax_Syntax.sigquals =
                                          uu____9968;
                                        FStar_Syntax_Syntax.sigmeta =
                                          uu____9969;
                                        FStar_Syntax_Syntax.sigattrs =
                                          uu____9970;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____9990 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____9990
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids,s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____10038 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____10045 -> cache t  in
                            let uu____10046 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____10046 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____10052 =
                                   let uu____10053 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____10053)
                                    in
                                 maybe_cache uu____10052)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____10121 = find_in_sigtab env lid  in
         match uu____10121 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10208) ->
          add_sigelts env ses
      | uu____10217 ->
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
            | uu____10231 -> ()))

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
        (fun uu___78_10262  ->
           match uu___78_10262 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____10280 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____10341,lb::[]),uu____10343) ->
            let uu____10350 =
              let uu____10359 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____10368 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____10359, uu____10368)  in
            FStar_Pervasives_Native.Some uu____10350
        | FStar_Syntax_Syntax.Sig_let ((uu____10381,lbs),uu____10383) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____10413 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____10425 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____10425
                     then
                       let uu____10436 =
                         let uu____10445 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____10454 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____10445, uu____10454)  in
                       FStar_Pervasives_Native.Some uu____10436
                     else FStar_Pervasives_Native.None)
        | uu____10476 -> FStar_Pervasives_Native.None
  
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
          let uu____10535 =
            let uu____10544 =
              let uu____10549 =
                let uu____10550 =
                  let uu____10553 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____10553
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____10550)  in
              inst_tscheme1 uu____10549  in
            (uu____10544, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____10535
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____10575,uu____10576) ->
          let uu____10581 =
            let uu____10590 =
              let uu____10595 =
                let uu____10596 =
                  let uu____10599 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____10599  in
                (us, uu____10596)  in
              inst_tscheme1 uu____10595  in
            (uu____10590, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____10581
      | uu____10618 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____10706 =
          match uu____10706 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____10802,uvs,t,uu____10805,uu____10806,uu____10807);
                      FStar_Syntax_Syntax.sigrng = uu____10808;
                      FStar_Syntax_Syntax.sigquals = uu____10809;
                      FStar_Syntax_Syntax.sigmeta = uu____10810;
                      FStar_Syntax_Syntax.sigattrs = uu____10811;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____10832 =
                     let uu____10841 = inst_tscheme1 (uvs, t)  in
                     (uu____10841, rng)  in
                   FStar_Pervasives_Native.Some uu____10832
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____10865;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____10867;
                      FStar_Syntax_Syntax.sigattrs = uu____10868;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____10885 =
                     let uu____10886 = in_cur_mod env l  in uu____10886 = Yes
                      in
                   if uu____10885
                   then
                     let uu____10897 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____10897
                      then
                        let uu____10910 =
                          let uu____10919 = inst_tscheme1 (uvs, t)  in
                          (uu____10919, rng)  in
                        FStar_Pervasives_Native.Some uu____10910
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10950 =
                        let uu____10959 = inst_tscheme1 (uvs, t)  in
                        (uu____10959, rng)  in
                      FStar_Pervasives_Native.Some uu____10950)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____10984,uu____10985);
                      FStar_Syntax_Syntax.sigrng = uu____10986;
                      FStar_Syntax_Syntax.sigquals = uu____10987;
                      FStar_Syntax_Syntax.sigmeta = uu____10988;
                      FStar_Syntax_Syntax.sigattrs = uu____10989;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____11028 =
                          let uu____11037 = inst_tscheme1 (uvs, k)  in
                          (uu____11037, rng)  in
                        FStar_Pervasives_Native.Some uu____11028
                    | uu____11058 ->
                        let uu____11059 =
                          let uu____11068 =
                            let uu____11073 =
                              let uu____11074 =
                                let uu____11077 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11077
                                 in
                              (uvs, uu____11074)  in
                            inst_tscheme1 uu____11073  in
                          (uu____11068, rng)  in
                        FStar_Pervasives_Native.Some uu____11059)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11100,uu____11101);
                      FStar_Syntax_Syntax.sigrng = uu____11102;
                      FStar_Syntax_Syntax.sigquals = uu____11103;
                      FStar_Syntax_Syntax.sigmeta = uu____11104;
                      FStar_Syntax_Syntax.sigattrs = uu____11105;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____11145 =
                          let uu____11154 = inst_tscheme_with (uvs, k) us  in
                          (uu____11154, rng)  in
                        FStar_Pervasives_Native.Some uu____11145
                    | uu____11175 ->
                        let uu____11176 =
                          let uu____11185 =
                            let uu____11190 =
                              let uu____11191 =
                                let uu____11194 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11194
                                 in
                              (uvs, uu____11191)  in
                            inst_tscheme_with uu____11190 us  in
                          (uu____11185, rng)  in
                        FStar_Pervasives_Native.Some uu____11176)
               | FStar_Util.Inr se ->
                   let uu____11230 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____11251;
                          FStar_Syntax_Syntax.sigrng = uu____11252;
                          FStar_Syntax_Syntax.sigquals = uu____11253;
                          FStar_Syntax_Syntax.sigmeta = uu____11254;
                          FStar_Syntax_Syntax.sigattrs = uu____11255;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____11270 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____11230
                     (FStar_Util.map_option
                        (fun uu____11318  ->
                           match uu____11318 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____11349 =
          let uu____11360 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____11360 mapper  in
        match uu____11349 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____11434 =
              let uu____11445 =
                let uu____11452 =
                  let uu___97_11455 = t  in
                  let uu____11456 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___97_11455.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____11456;
                    FStar_Syntax_Syntax.vars =
                      (uu___97_11455.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____11452)  in
              (uu____11445, r)  in
            FStar_Pervasives_Native.Some uu____11434
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11503 = lookup_qname env l  in
      match uu____11503 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____11522 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____11574 = try_lookup_bv env bv  in
      match uu____11574 with
      | FStar_Pervasives_Native.None  ->
          let uu____11589 = variable_not_found bv  in
          FStar_Errors.raise_error uu____11589 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____11604 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____11605 =
            let uu____11606 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____11606  in
          (uu____11604, uu____11605)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____11627 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____11627 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____11693 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____11693  in
          let uu____11694 =
            let uu____11703 =
              let uu____11708 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____11708)  in
            (uu____11703, r1)  in
          FStar_Pervasives_Native.Some uu____11694
  
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
        let uu____11742 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____11742 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____11775,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____11800 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____11800  in
            let uu____11801 =
              let uu____11806 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____11806, r1)  in
            FStar_Pervasives_Native.Some uu____11801
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____11829 = try_lookup_lid env l  in
      match uu____11829 with
      | FStar_Pervasives_Native.None  ->
          let uu____11856 = name_not_found l  in
          let uu____11861 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____11856 uu____11861
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___79_11901  ->
              match uu___79_11901 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____11903 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____11922 = lookup_qname env lid  in
      match uu____11922 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11931,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____11934;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11936;
              FStar_Syntax_Syntax.sigattrs = uu____11937;_},FStar_Pervasives_Native.None
            ),uu____11938)
          ->
          let uu____11987 =
            let uu____11994 =
              let uu____11995 =
                let uu____11998 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____11998 t  in
              (uvs, uu____11995)  in
            (uu____11994, q)  in
          FStar_Pervasives_Native.Some uu____11987
      | uu____12011 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12032 = lookup_qname env lid  in
      match uu____12032 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12037,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12040;
              FStar_Syntax_Syntax.sigquals = uu____12041;
              FStar_Syntax_Syntax.sigmeta = uu____12042;
              FStar_Syntax_Syntax.sigattrs = uu____12043;_},FStar_Pervasives_Native.None
            ),uu____12044)
          ->
          let uu____12093 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12093 (uvs, t)
      | uu____12098 ->
          let uu____12099 = name_not_found lid  in
          let uu____12104 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12099 uu____12104
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12123 = lookup_qname env lid  in
      match uu____12123 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12128,uvs,t,uu____12131,uu____12132,uu____12133);
              FStar_Syntax_Syntax.sigrng = uu____12134;
              FStar_Syntax_Syntax.sigquals = uu____12135;
              FStar_Syntax_Syntax.sigmeta = uu____12136;
              FStar_Syntax_Syntax.sigattrs = uu____12137;_},FStar_Pervasives_Native.None
            ),uu____12138)
          ->
          let uu____12191 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12191 (uvs, t)
      | uu____12196 ->
          let uu____12197 = name_not_found lid  in
          let uu____12202 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12197 uu____12202
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12223 = lookup_qname env lid  in
      match uu____12223 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12230,uu____12231,uu____12232,uu____12233,uu____12234,dcs);
              FStar_Syntax_Syntax.sigrng = uu____12236;
              FStar_Syntax_Syntax.sigquals = uu____12237;
              FStar_Syntax_Syntax.sigmeta = uu____12238;
              FStar_Syntax_Syntax.sigattrs = uu____12239;_},uu____12240),uu____12241)
          -> (true, dcs)
      | uu____12302 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____12315 = lookup_qname env lid  in
      match uu____12315 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12316,uu____12317,uu____12318,l,uu____12320,uu____12321);
              FStar_Syntax_Syntax.sigrng = uu____12322;
              FStar_Syntax_Syntax.sigquals = uu____12323;
              FStar_Syntax_Syntax.sigmeta = uu____12324;
              FStar_Syntax_Syntax.sigattrs = uu____12325;_},uu____12326),uu____12327)
          -> l
      | uu____12382 ->
          let uu____12383 =
            let uu____12384 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____12384  in
          failwith uu____12383
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____12433)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____12484,lbs),uu____12486)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____12508 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____12508
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____12540 -> FStar_Pervasives_Native.None)
        | uu____12545 -> FStar_Pervasives_Native.None
  
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
        let uu____12575 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____12575
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____12600),uu____12601) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____12650 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12671 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____12671
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____12690 = lookup_qname env ftv  in
      match uu____12690 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____12694) ->
          let uu____12739 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____12739 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____12760,t),r) ->
               let uu____12775 =
                 let uu____12776 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____12776 t  in
               FStar_Pervasives_Native.Some uu____12775)
      | uu____12777 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____12788 = try_lookup_effect_lid env ftv  in
      match uu____12788 with
      | FStar_Pervasives_Native.None  ->
          let uu____12791 = name_not_found ftv  in
          let uu____12796 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____12791 uu____12796
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
        let uu____12819 = lookup_qname env lid0  in
        match uu____12819 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____12830);
                FStar_Syntax_Syntax.sigrng = uu____12831;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____12833;
                FStar_Syntax_Syntax.sigattrs = uu____12834;_},FStar_Pervasives_Native.None
              ),uu____12835)
            ->
            let lid1 =
              let uu____12889 =
                let uu____12890 = FStar_Ident.range_of_lid lid  in
                let uu____12891 =
                  let uu____12892 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____12892  in
                FStar_Range.set_use_range uu____12890 uu____12891  in
              FStar_Ident.set_lid_range lid uu____12889  in
            let uu____12893 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___80_12897  ->
                      match uu___80_12897 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12898 -> false))
               in
            if uu____12893
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____12912 =
                      let uu____12913 =
                        let uu____12914 = get_range env  in
                        FStar_Range.string_of_range uu____12914  in
                      let uu____12915 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____12916 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____12913 uu____12915 uu____12916
                       in
                    failwith uu____12912)
                  in
               match (binders, univs1) with
               | ([],uu____12931) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____12952,uu____12953::uu____12954::uu____12955) ->
                   let uu____12972 =
                     let uu____12973 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____12974 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____12973 uu____12974
                      in
                   failwith uu____12972
               | uu____12981 ->
                   let uu____12994 =
                     let uu____12999 =
                       let uu____13000 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____13000)  in
                     inst_tscheme_with uu____12999 insts  in
                   (match uu____12994 with
                    | (uu____13013,t) ->
                        let t1 =
                          let uu____13016 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____13016 t  in
                        let uu____13017 =
                          let uu____13018 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13018.FStar_Syntax_Syntax.n  in
                        (match uu____13017 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____13049 -> failwith "Impossible")))
        | uu____13056 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____13079 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____13079 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____13092,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____13099 = find1 l2  in
            (match uu____13099 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____13106 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____13106 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____13110 = find1 l  in
            (match uu____13110 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____13115 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____13115
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____13129 = lookup_qname env l1  in
      match uu____13129 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____13132;
              FStar_Syntax_Syntax.sigrng = uu____13133;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13135;
              FStar_Syntax_Syntax.sigattrs = uu____13136;_},uu____13137),uu____13138)
          -> q
      | uu____13189 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____13210 =
          let uu____13211 =
            let uu____13212 = FStar_Util.string_of_int i  in
            let uu____13213 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____13212 uu____13213
             in
          failwith uu____13211  in
        let uu____13214 = lookup_datacon env lid  in
        match uu____13214 with
        | (uu____13219,t) ->
            let uu____13221 =
              let uu____13222 = FStar_Syntax_Subst.compress t  in
              uu____13222.FStar_Syntax_Syntax.n  in
            (match uu____13221 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____13226) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____13257 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____13257
                      FStar_Pervasives_Native.fst)
             | uu____13266 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13277 = lookup_qname env l  in
      match uu____13277 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13278,uu____13279,uu____13280);
              FStar_Syntax_Syntax.sigrng = uu____13281;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13283;
              FStar_Syntax_Syntax.sigattrs = uu____13284;_},uu____13285),uu____13286)
          ->
          FStar_Util.for_some
            (fun uu___81_13339  ->
               match uu___81_13339 with
               | FStar_Syntax_Syntax.Projector uu____13340 -> true
               | uu____13345 -> false) quals
      | uu____13346 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13357 = lookup_qname env lid  in
      match uu____13357 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13358,uu____13359,uu____13360,uu____13361,uu____13362,uu____13363);
              FStar_Syntax_Syntax.sigrng = uu____13364;
              FStar_Syntax_Syntax.sigquals = uu____13365;
              FStar_Syntax_Syntax.sigmeta = uu____13366;
              FStar_Syntax_Syntax.sigattrs = uu____13367;_},uu____13368),uu____13369)
          -> true
      | uu____13424 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13435 = lookup_qname env lid  in
      match uu____13435 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13436,uu____13437,uu____13438,uu____13439,uu____13440,uu____13441);
              FStar_Syntax_Syntax.sigrng = uu____13442;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13444;
              FStar_Syntax_Syntax.sigattrs = uu____13445;_},uu____13446),uu____13447)
          ->
          FStar_Util.for_some
            (fun uu___82_13508  ->
               match uu___82_13508 with
               | FStar_Syntax_Syntax.RecordType uu____13509 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____13518 -> true
               | uu____13527 -> false) quals
      | uu____13528 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____13534,uu____13535);
            FStar_Syntax_Syntax.sigrng = uu____13536;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____13538;
            FStar_Syntax_Syntax.sigattrs = uu____13539;_},uu____13540),uu____13541)
        ->
        FStar_Util.for_some
          (fun uu___83_13598  ->
             match uu___83_13598 with
             | FStar_Syntax_Syntax.Action uu____13599 -> true
             | uu____13600 -> false) quals
    | uu____13601 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13612 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____13612
  
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
      let uu____13626 =
        let uu____13627 = FStar_Syntax_Util.un_uinst head1  in
        uu____13627.FStar_Syntax_Syntax.n  in
      match uu____13626 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____13631 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13642 = lookup_qname env l  in
      match uu____13642 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____13644),uu____13645) ->
          FStar_Util.for_some
            (fun uu___84_13693  ->
               match uu___84_13693 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____13694 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____13695 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____13766 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____13782) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____13799 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____13806 ->
                 FStar_Pervasives_Native.Some true
             | uu____13823 -> FStar_Pervasives_Native.Some false)
         in
      let uu____13824 =
        let uu____13827 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____13827 mapper  in
      match uu____13824 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____13877 = lookup_qname env lid  in
      match uu____13877 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13878,uu____13879,tps,uu____13881,uu____13882,uu____13883);
              FStar_Syntax_Syntax.sigrng = uu____13884;
              FStar_Syntax_Syntax.sigquals = uu____13885;
              FStar_Syntax_Syntax.sigmeta = uu____13886;
              FStar_Syntax_Syntax.sigattrs = uu____13887;_},uu____13888),uu____13889)
          -> FStar_List.length tps
      | uu____13952 ->
          let uu____13953 = name_not_found lid  in
          let uu____13958 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13953 uu____13958
  
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
           (fun uu____14002  ->
              match uu____14002 with
              | (d,uu____14010) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____14025 = effect_decl_opt env l  in
      match uu____14025 with
      | FStar_Pervasives_Native.None  ->
          let uu____14040 = name_not_found l  in
          let uu____14045 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14040 uu____14045
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____14067  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____14086  ->
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
        let uu____14117 = FStar_Ident.lid_equals l1 l2  in
        if uu____14117
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____14125 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____14125
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____14133 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____14186  ->
                        match uu____14186 with
                        | (m1,m2,uu____14199,uu____14200,uu____14201) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____14133 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14218 =
                    let uu____14223 =
                      let uu____14224 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____14225 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____14224
                        uu____14225
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____14223)
                     in
                  FStar_Errors.raise_error uu____14218 env.range
              | FStar_Pervasives_Native.Some
                  (uu____14232,uu____14233,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____14266 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____14266
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
  'Auu____14282 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____14282)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____14311 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____14337  ->
                match uu____14337 with
                | (d,uu____14343) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____14311 with
      | FStar_Pervasives_Native.None  ->
          let uu____14354 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____14354
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____14367 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____14367 with
           | (uu____14382,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____14398)::(wp,uu____14400)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____14436 -> failwith "Impossible"))
  
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
          let uu____14489 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____14489
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____14491 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____14491
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
                  let uu____14499 = get_range env  in
                  let uu____14500 =
                    let uu____14507 =
                      let uu____14508 =
                        let uu____14523 =
                          let uu____14532 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____14532]  in
                        (null_wp, uu____14523)  in
                      FStar_Syntax_Syntax.Tm_app uu____14508  in
                    FStar_Syntax_Syntax.mk uu____14507  in
                  uu____14500 FStar_Pervasives_Native.None uu____14499  in
                let uu____14564 =
                  let uu____14565 =
                    let uu____14574 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____14574]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____14565;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____14564))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___98_14605 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___98_14605.order);
              joins = (uu___98_14605.joins)
            }  in
          let uu___99_14614 = env  in
          {
            solver = (uu___99_14614.solver);
            range = (uu___99_14614.range);
            curmodule = (uu___99_14614.curmodule);
            gamma = (uu___99_14614.gamma);
            gamma_sig = (uu___99_14614.gamma_sig);
            gamma_cache = (uu___99_14614.gamma_cache);
            modules = (uu___99_14614.modules);
            expected_typ = (uu___99_14614.expected_typ);
            sigtab = (uu___99_14614.sigtab);
            is_pattern = (uu___99_14614.is_pattern);
            instantiate_imp = (uu___99_14614.instantiate_imp);
            effects;
            generalize = (uu___99_14614.generalize);
            letrecs = (uu___99_14614.letrecs);
            top_level = (uu___99_14614.top_level);
            check_uvars = (uu___99_14614.check_uvars);
            use_eq = (uu___99_14614.use_eq);
            is_iface = (uu___99_14614.is_iface);
            admit = (uu___99_14614.admit);
            lax = (uu___99_14614.lax);
            lax_universes = (uu___99_14614.lax_universes);
            failhard = (uu___99_14614.failhard);
            nosynth = (uu___99_14614.nosynth);
            tc_term = (uu___99_14614.tc_term);
            type_of = (uu___99_14614.type_of);
            universe_of = (uu___99_14614.universe_of);
            check_type_of = (uu___99_14614.check_type_of);
            use_bv_sorts = (uu___99_14614.use_bv_sorts);
            qtbl_name_and_index = (uu___99_14614.qtbl_name_and_index);
            normalized_eff_names = (uu___99_14614.normalized_eff_names);
            proof_ns = (uu___99_14614.proof_ns);
            synth_hook = (uu___99_14614.synth_hook);
            splice = (uu___99_14614.splice);
            is_native_tactic = (uu___99_14614.is_native_tactic);
            identifier_info = (uu___99_14614.identifier_info);
            tc_hooks = (uu___99_14614.tc_hooks);
            dsenv = (uu___99_14614.dsenv);
            dep_graph = (uu___99_14614.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____14644 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____14644  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____14802 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____14803 = l1 u t wp e  in
                                l2 u t uu____14802 uu____14803))
                | uu____14804 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____14876 = inst_tscheme_with lift_t [u]  in
            match uu____14876 with
            | (uu____14883,lift_t1) ->
                let uu____14885 =
                  let uu____14892 =
                    let uu____14893 =
                      let uu____14908 =
                        let uu____14917 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____14924 =
                          let uu____14933 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____14933]  in
                        uu____14917 :: uu____14924  in
                      (lift_t1, uu____14908)  in
                    FStar_Syntax_Syntax.Tm_app uu____14893  in
                  FStar_Syntax_Syntax.mk uu____14892  in
                uu____14885 FStar_Pervasives_Native.None
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
            let uu____15041 = inst_tscheme_with lift_t [u]  in
            match uu____15041 with
            | (uu____15048,lift_t1) ->
                let uu____15050 =
                  let uu____15057 =
                    let uu____15058 =
                      let uu____15073 =
                        let uu____15082 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15089 =
                          let uu____15098 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____15105 =
                            let uu____15114 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____15114]  in
                          uu____15098 :: uu____15105  in
                        uu____15082 :: uu____15089  in
                      (lift_t1, uu____15073)  in
                    FStar_Syntax_Syntax.Tm_app uu____15058  in
                  FStar_Syntax_Syntax.mk uu____15057  in
                uu____15050 FStar_Pervasives_Native.None
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
              let uu____15204 =
                let uu____15205 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____15205
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____15204  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____15209 =
              let uu____15210 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____15210  in
            let uu____15211 =
              let uu____15212 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____15238 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____15238)
                 in
              FStar_Util.dflt "none" uu____15212  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____15209
              uu____15211
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____15264  ->
                    match uu____15264 with
                    | (e,uu____15272) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____15295 =
            match uu____15295 with
            | (i,j) ->
                let uu____15306 = FStar_Ident.lid_equals i j  in
                if uu____15306
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
              let uu____15338 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____15348 = FStar_Ident.lid_equals i k  in
                        if uu____15348
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____15359 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____15359
                                  then []
                                  else
                                    (let uu____15363 =
                                       let uu____15372 =
                                         find_edge order1 (i, k)  in
                                       let uu____15375 =
                                         find_edge order1 (k, j)  in
                                       (uu____15372, uu____15375)  in
                                     match uu____15363 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____15390 =
                                           compose_edges e1 e2  in
                                         [uu____15390]
                                     | uu____15391 -> [])))))
                 in
              FStar_List.append order1 uu____15338  in
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
                   let uu____15421 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____15423 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____15423
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____15421
                   then
                     let uu____15428 =
                       let uu____15433 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____15433)
                        in
                     let uu____15434 = get_range env  in
                     FStar_Errors.raise_error uu____15428 uu____15434
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____15511 = FStar_Ident.lid_equals i j
                                   in
                                if uu____15511
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____15560 =
                                              let uu____15569 =
                                                find_edge order2 (i, k)  in
                                              let uu____15572 =
                                                find_edge order2 (j, k)  in
                                              (uu____15569, uu____15572)  in
                                            match uu____15560 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____15614,uu____15615)
                                                     ->
                                                     let uu____15622 =
                                                       let uu____15627 =
                                                         let uu____15628 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____15628
                                                          in
                                                       let uu____15631 =
                                                         let uu____15632 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____15632
                                                          in
                                                       (uu____15627,
                                                         uu____15631)
                                                        in
                                                     (match uu____15622 with
                                                      | (true ,true ) ->
                                                          let uu____15643 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____15643
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
                                            | uu____15668 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___100_15741 = env.effects  in
              { decls = (uu___100_15741.decls); order = order2; joins }  in
            let uu___101_15742 = env  in
            {
              solver = (uu___101_15742.solver);
              range = (uu___101_15742.range);
              curmodule = (uu___101_15742.curmodule);
              gamma = (uu___101_15742.gamma);
              gamma_sig = (uu___101_15742.gamma_sig);
              gamma_cache = (uu___101_15742.gamma_cache);
              modules = (uu___101_15742.modules);
              expected_typ = (uu___101_15742.expected_typ);
              sigtab = (uu___101_15742.sigtab);
              is_pattern = (uu___101_15742.is_pattern);
              instantiate_imp = (uu___101_15742.instantiate_imp);
              effects;
              generalize = (uu___101_15742.generalize);
              letrecs = (uu___101_15742.letrecs);
              top_level = (uu___101_15742.top_level);
              check_uvars = (uu___101_15742.check_uvars);
              use_eq = (uu___101_15742.use_eq);
              is_iface = (uu___101_15742.is_iface);
              admit = (uu___101_15742.admit);
              lax = (uu___101_15742.lax);
              lax_universes = (uu___101_15742.lax_universes);
              failhard = (uu___101_15742.failhard);
              nosynth = (uu___101_15742.nosynth);
              tc_term = (uu___101_15742.tc_term);
              type_of = (uu___101_15742.type_of);
              universe_of = (uu___101_15742.universe_of);
              check_type_of = (uu___101_15742.check_type_of);
              use_bv_sorts = (uu___101_15742.use_bv_sorts);
              qtbl_name_and_index = (uu___101_15742.qtbl_name_and_index);
              normalized_eff_names = (uu___101_15742.normalized_eff_names);
              proof_ns = (uu___101_15742.proof_ns);
              synth_hook = (uu___101_15742.synth_hook);
              splice = (uu___101_15742.splice);
              is_native_tactic = (uu___101_15742.is_native_tactic);
              identifier_info = (uu___101_15742.identifier_info);
              tc_hooks = (uu___101_15742.tc_hooks);
              dsenv = (uu___101_15742.dsenv);
              dep_graph = (uu___101_15742.dep_graph)
            }))
      | uu____15743 -> env
  
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
        | uu____15771 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____15783 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____15783 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____15800 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____15800 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____15819 =
                     let uu____15824 =
                       let uu____15825 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____15830 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____15837 =
                         let uu____15838 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____15838  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____15825 uu____15830 uu____15837
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____15824)
                      in
                   FStar_Errors.raise_error uu____15819
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____15843 =
                     let uu____15852 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____15852 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____15881  ->
                        fun uu____15882  ->
                          match (uu____15881, uu____15882) with
                          | ((x,uu____15904),(t,uu____15906)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____15843
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____15925 =
                     let uu___102_15926 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___102_15926.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___102_15926.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___102_15926.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___102_15926.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____15925
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
          let uu____15956 = effect_decl_opt env effect_name  in
          match uu____15956 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____15989 =
                only_reifiable &&
                  (let uu____15991 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____15991)
                 in
              if uu____15989
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____16007 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____16026 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____16055 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____16055
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____16056 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____16056
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____16068 =
                       let uu____16071 = get_range env  in
                       let uu____16072 =
                         let uu____16079 =
                           let uu____16080 =
                             let uu____16095 =
                               let uu____16104 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____16104; wp]  in
                             (repr, uu____16095)  in
                           FStar_Syntax_Syntax.Tm_app uu____16080  in
                         FStar_Syntax_Syntax.mk uu____16079  in
                       uu____16072 FStar_Pervasives_Native.None uu____16071
                        in
                     FStar_Pervasives_Native.Some uu____16068)
  
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
          let uu____16184 =
            let uu____16189 =
              let uu____16190 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____16190
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____16189)  in
          let uu____16191 = get_range env  in
          FStar_Errors.raise_error uu____16184 uu____16191  in
        let uu____16192 = effect_repr_aux true env c u_c  in
        match uu____16192 with
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
      | uu____16238 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____16249 =
        let uu____16250 = FStar_Syntax_Subst.compress t  in
        uu____16250.FStar_Syntax_Syntax.n  in
      match uu____16249 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____16253,c) ->
          is_reifiable_comp env c
      | uu____16271 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___103_16292 = env  in
        {
          solver = (uu___103_16292.solver);
          range = (uu___103_16292.range);
          curmodule = (uu___103_16292.curmodule);
          gamma = (uu___103_16292.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___103_16292.gamma_cache);
          modules = (uu___103_16292.modules);
          expected_typ = (uu___103_16292.expected_typ);
          sigtab = (uu___103_16292.sigtab);
          is_pattern = (uu___103_16292.is_pattern);
          instantiate_imp = (uu___103_16292.instantiate_imp);
          effects = (uu___103_16292.effects);
          generalize = (uu___103_16292.generalize);
          letrecs = (uu___103_16292.letrecs);
          top_level = (uu___103_16292.top_level);
          check_uvars = (uu___103_16292.check_uvars);
          use_eq = (uu___103_16292.use_eq);
          is_iface = (uu___103_16292.is_iface);
          admit = (uu___103_16292.admit);
          lax = (uu___103_16292.lax);
          lax_universes = (uu___103_16292.lax_universes);
          failhard = (uu___103_16292.failhard);
          nosynth = (uu___103_16292.nosynth);
          tc_term = (uu___103_16292.tc_term);
          type_of = (uu___103_16292.type_of);
          universe_of = (uu___103_16292.universe_of);
          check_type_of = (uu___103_16292.check_type_of);
          use_bv_sorts = (uu___103_16292.use_bv_sorts);
          qtbl_name_and_index = (uu___103_16292.qtbl_name_and_index);
          normalized_eff_names = (uu___103_16292.normalized_eff_names);
          proof_ns = (uu___103_16292.proof_ns);
          synth_hook = (uu___103_16292.synth_hook);
          splice = (uu___103_16292.splice);
          is_native_tactic = (uu___103_16292.is_native_tactic);
          identifier_info = (uu___103_16292.identifier_info);
          tc_hooks = (uu___103_16292.tc_hooks);
          dsenv = (uu___103_16292.dsenv);
          dep_graph = (uu___103_16292.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___104_16304 = env  in
      {
        solver = (uu___104_16304.solver);
        range = (uu___104_16304.range);
        curmodule = (uu___104_16304.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___104_16304.gamma_sig);
        gamma_cache = (uu___104_16304.gamma_cache);
        modules = (uu___104_16304.modules);
        expected_typ = (uu___104_16304.expected_typ);
        sigtab = (uu___104_16304.sigtab);
        is_pattern = (uu___104_16304.is_pattern);
        instantiate_imp = (uu___104_16304.instantiate_imp);
        effects = (uu___104_16304.effects);
        generalize = (uu___104_16304.generalize);
        letrecs = (uu___104_16304.letrecs);
        top_level = (uu___104_16304.top_level);
        check_uvars = (uu___104_16304.check_uvars);
        use_eq = (uu___104_16304.use_eq);
        is_iface = (uu___104_16304.is_iface);
        admit = (uu___104_16304.admit);
        lax = (uu___104_16304.lax);
        lax_universes = (uu___104_16304.lax_universes);
        failhard = (uu___104_16304.failhard);
        nosynth = (uu___104_16304.nosynth);
        tc_term = (uu___104_16304.tc_term);
        type_of = (uu___104_16304.type_of);
        universe_of = (uu___104_16304.universe_of);
        check_type_of = (uu___104_16304.check_type_of);
        use_bv_sorts = (uu___104_16304.use_bv_sorts);
        qtbl_name_and_index = (uu___104_16304.qtbl_name_and_index);
        normalized_eff_names = (uu___104_16304.normalized_eff_names);
        proof_ns = (uu___104_16304.proof_ns);
        synth_hook = (uu___104_16304.synth_hook);
        splice = (uu___104_16304.splice);
        is_native_tactic = (uu___104_16304.is_native_tactic);
        identifier_info = (uu___104_16304.identifier_info);
        tc_hooks = (uu___104_16304.tc_hooks);
        dsenv = (uu___104_16304.dsenv);
        dep_graph = (uu___104_16304.dep_graph)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
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
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___105_16359 = env  in
             {
               solver = (uu___105_16359.solver);
               range = (uu___105_16359.range);
               curmodule = (uu___105_16359.curmodule);
               gamma = rest;
               gamma_sig = (uu___105_16359.gamma_sig);
               gamma_cache = (uu___105_16359.gamma_cache);
               modules = (uu___105_16359.modules);
               expected_typ = (uu___105_16359.expected_typ);
               sigtab = (uu___105_16359.sigtab);
               is_pattern = (uu___105_16359.is_pattern);
               instantiate_imp = (uu___105_16359.instantiate_imp);
               effects = (uu___105_16359.effects);
               generalize = (uu___105_16359.generalize);
               letrecs = (uu___105_16359.letrecs);
               top_level = (uu___105_16359.top_level);
               check_uvars = (uu___105_16359.check_uvars);
               use_eq = (uu___105_16359.use_eq);
               is_iface = (uu___105_16359.is_iface);
               admit = (uu___105_16359.admit);
               lax = (uu___105_16359.lax);
               lax_universes = (uu___105_16359.lax_universes);
               failhard = (uu___105_16359.failhard);
               nosynth = (uu___105_16359.nosynth);
               tc_term = (uu___105_16359.tc_term);
               type_of = (uu___105_16359.type_of);
               universe_of = (uu___105_16359.universe_of);
               check_type_of = (uu___105_16359.check_type_of);
               use_bv_sorts = (uu___105_16359.use_bv_sorts);
               qtbl_name_and_index = (uu___105_16359.qtbl_name_and_index);
               normalized_eff_names = (uu___105_16359.normalized_eff_names);
               proof_ns = (uu___105_16359.proof_ns);
               synth_hook = (uu___105_16359.synth_hook);
               splice = (uu___105_16359.splice);
               is_native_tactic = (uu___105_16359.is_native_tactic);
               identifier_info = (uu___105_16359.identifier_info);
               tc_hooks = (uu___105_16359.tc_hooks);
               dsenv = (uu___105_16359.dsenv);
               dep_graph = (uu___105_16359.dep_graph)
             }))
    | uu____16360 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____16386  ->
             match uu____16386 with | (x,uu____16392) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___106_16422 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_16422.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_16422.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___107_16462 = env  in
       {
         solver = (uu___107_16462.solver);
         range = (uu___107_16462.range);
         curmodule = (uu___107_16462.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___107_16462.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___107_16462.sigtab);
         is_pattern = (uu___107_16462.is_pattern);
         instantiate_imp = (uu___107_16462.instantiate_imp);
         effects = (uu___107_16462.effects);
         generalize = (uu___107_16462.generalize);
         letrecs = (uu___107_16462.letrecs);
         top_level = (uu___107_16462.top_level);
         check_uvars = (uu___107_16462.check_uvars);
         use_eq = (uu___107_16462.use_eq);
         is_iface = (uu___107_16462.is_iface);
         admit = (uu___107_16462.admit);
         lax = (uu___107_16462.lax);
         lax_universes = (uu___107_16462.lax_universes);
         failhard = (uu___107_16462.failhard);
         nosynth = (uu___107_16462.nosynth);
         tc_term = (uu___107_16462.tc_term);
         type_of = (uu___107_16462.type_of);
         universe_of = (uu___107_16462.universe_of);
         check_type_of = (uu___107_16462.check_type_of);
         use_bv_sorts = (uu___107_16462.use_bv_sorts);
         qtbl_name_and_index = (uu___107_16462.qtbl_name_and_index);
         normalized_eff_names = (uu___107_16462.normalized_eff_names);
         proof_ns = (uu___107_16462.proof_ns);
         synth_hook = (uu___107_16462.synth_hook);
         splice = (uu___107_16462.splice);
         is_native_tactic = (uu___107_16462.is_native_tactic);
         identifier_info = (uu___107_16462.identifier_info);
         tc_hooks = (uu___107_16462.tc_hooks);
         dsenv = (uu___107_16462.dsenv);
         dep_graph = (uu___107_16462.dep_graph)
       })
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
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
        let uu____16504 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____16504 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____16532 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____16532)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___108_16547 = env  in
      {
        solver = (uu___108_16547.solver);
        range = (uu___108_16547.range);
        curmodule = (uu___108_16547.curmodule);
        gamma = (uu___108_16547.gamma);
        gamma_sig = (uu___108_16547.gamma_sig);
        gamma_cache = (uu___108_16547.gamma_cache);
        modules = (uu___108_16547.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___108_16547.sigtab);
        is_pattern = (uu___108_16547.is_pattern);
        instantiate_imp = (uu___108_16547.instantiate_imp);
        effects = (uu___108_16547.effects);
        generalize = (uu___108_16547.generalize);
        letrecs = (uu___108_16547.letrecs);
        top_level = (uu___108_16547.top_level);
        check_uvars = (uu___108_16547.check_uvars);
        use_eq = false;
        is_iface = (uu___108_16547.is_iface);
        admit = (uu___108_16547.admit);
        lax = (uu___108_16547.lax);
        lax_universes = (uu___108_16547.lax_universes);
        failhard = (uu___108_16547.failhard);
        nosynth = (uu___108_16547.nosynth);
        tc_term = (uu___108_16547.tc_term);
        type_of = (uu___108_16547.type_of);
        universe_of = (uu___108_16547.universe_of);
        check_type_of = (uu___108_16547.check_type_of);
        use_bv_sorts = (uu___108_16547.use_bv_sorts);
        qtbl_name_and_index = (uu___108_16547.qtbl_name_and_index);
        normalized_eff_names = (uu___108_16547.normalized_eff_names);
        proof_ns = (uu___108_16547.proof_ns);
        synth_hook = (uu___108_16547.synth_hook);
        splice = (uu___108_16547.splice);
        is_native_tactic = (uu___108_16547.is_native_tactic);
        identifier_info = (uu___108_16547.identifier_info);
        tc_hooks = (uu___108_16547.tc_hooks);
        dsenv = (uu___108_16547.dsenv);
        dep_graph = (uu___108_16547.dep_graph)
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
    let uu____16575 = expected_typ env_  in
    ((let uu___109_16581 = env_  in
      {
        solver = (uu___109_16581.solver);
        range = (uu___109_16581.range);
        curmodule = (uu___109_16581.curmodule);
        gamma = (uu___109_16581.gamma);
        gamma_sig = (uu___109_16581.gamma_sig);
        gamma_cache = (uu___109_16581.gamma_cache);
        modules = (uu___109_16581.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___109_16581.sigtab);
        is_pattern = (uu___109_16581.is_pattern);
        instantiate_imp = (uu___109_16581.instantiate_imp);
        effects = (uu___109_16581.effects);
        generalize = (uu___109_16581.generalize);
        letrecs = (uu___109_16581.letrecs);
        top_level = (uu___109_16581.top_level);
        check_uvars = (uu___109_16581.check_uvars);
        use_eq = false;
        is_iface = (uu___109_16581.is_iface);
        admit = (uu___109_16581.admit);
        lax = (uu___109_16581.lax);
        lax_universes = (uu___109_16581.lax_universes);
        failhard = (uu___109_16581.failhard);
        nosynth = (uu___109_16581.nosynth);
        tc_term = (uu___109_16581.tc_term);
        type_of = (uu___109_16581.type_of);
        universe_of = (uu___109_16581.universe_of);
        check_type_of = (uu___109_16581.check_type_of);
        use_bv_sorts = (uu___109_16581.use_bv_sorts);
        qtbl_name_and_index = (uu___109_16581.qtbl_name_and_index);
        normalized_eff_names = (uu___109_16581.normalized_eff_names);
        proof_ns = (uu___109_16581.proof_ns);
        synth_hook = (uu___109_16581.synth_hook);
        splice = (uu___109_16581.splice);
        is_native_tactic = (uu___109_16581.is_native_tactic);
        identifier_info = (uu___109_16581.identifier_info);
        tc_hooks = (uu___109_16581.tc_hooks);
        dsenv = (uu___109_16581.dsenv);
        dep_graph = (uu___109_16581.dep_graph)
      }), uu____16575)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____16591 =
      let uu____16594 = FStar_Ident.id_of_text ""  in [uu____16594]  in
    FStar_Ident.lid_of_ids uu____16591  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____16600 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16600
        then
          let uu____16603 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____16603 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___110_16630 = env  in
       {
         solver = (uu___110_16630.solver);
         range = (uu___110_16630.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___110_16630.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___110_16630.expected_typ);
         sigtab = (uu___110_16630.sigtab);
         is_pattern = (uu___110_16630.is_pattern);
         instantiate_imp = (uu___110_16630.instantiate_imp);
         effects = (uu___110_16630.effects);
         generalize = (uu___110_16630.generalize);
         letrecs = (uu___110_16630.letrecs);
         top_level = (uu___110_16630.top_level);
         check_uvars = (uu___110_16630.check_uvars);
         use_eq = (uu___110_16630.use_eq);
         is_iface = (uu___110_16630.is_iface);
         admit = (uu___110_16630.admit);
         lax = (uu___110_16630.lax);
         lax_universes = (uu___110_16630.lax_universes);
         failhard = (uu___110_16630.failhard);
         nosynth = (uu___110_16630.nosynth);
         tc_term = (uu___110_16630.tc_term);
         type_of = (uu___110_16630.type_of);
         universe_of = (uu___110_16630.universe_of);
         check_type_of = (uu___110_16630.check_type_of);
         use_bv_sorts = (uu___110_16630.use_bv_sorts);
         qtbl_name_and_index = (uu___110_16630.qtbl_name_and_index);
         normalized_eff_names = (uu___110_16630.normalized_eff_names);
         proof_ns = (uu___110_16630.proof_ns);
         synth_hook = (uu___110_16630.synth_hook);
         splice = (uu___110_16630.splice);
         is_native_tactic = (uu___110_16630.is_native_tactic);
         identifier_info = (uu___110_16630.identifier_info);
         tc_hooks = (uu___110_16630.tc_hooks);
         dsenv = (uu___110_16630.dsenv);
         dep_graph = (uu___110_16630.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____16681)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____16685,(uu____16686,t)))::tl1
          ->
          let uu____16707 =
            let uu____16710 = FStar_Syntax_Free.uvars t  in
            ext out uu____16710  in
          aux uu____16707 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16713;
            FStar_Syntax_Syntax.index = uu____16714;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16721 =
            let uu____16724 = FStar_Syntax_Free.uvars t  in
            ext out uu____16724  in
          aux uu____16721 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____16781)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____16785,(uu____16786,t)))::tl1
          ->
          let uu____16807 =
            let uu____16810 = FStar_Syntax_Free.univs t  in
            ext out uu____16810  in
          aux uu____16807 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16813;
            FStar_Syntax_Syntax.index = uu____16814;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16821 =
            let uu____16824 = FStar_Syntax_Free.univs t  in
            ext out uu____16824  in
          aux uu____16821 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____16885 = FStar_Util.set_add uname out  in
          aux uu____16885 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____16888,(uu____16889,t)))::tl1
          ->
          let uu____16910 =
            let uu____16913 = FStar_Syntax_Free.univnames t  in
            ext out uu____16913  in
          aux uu____16910 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16916;
            FStar_Syntax_Syntax.index = uu____16917;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16924 =
            let uu____16927 = FStar_Syntax_Free.univnames t  in
            ext out uu____16927  in
          aux uu____16924 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___85_16947  ->
            match uu___85_16947 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____16951 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____16964 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____16974 =
      let uu____16981 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____16981
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____16974 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____17019 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___86_17029  ->
              match uu___86_17029 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____17031 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____17031
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____17034) ->
                  let uu____17051 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____17051))
       in
    FStar_All.pipe_right uu____17019 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___87_17058  ->
    match uu___87_17058 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____17059 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____17079  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____17121) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____17140,uu____17141) -> false  in
      let uu____17150 =
        FStar_List.tryFind
          (fun uu____17168  ->
             match uu____17168 with | (p,uu____17176) -> list_prefix p path)
          env.proof_ns
         in
      match uu____17150 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____17187,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17209 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____17209
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___111_17227 = e  in
        {
          solver = (uu___111_17227.solver);
          range = (uu___111_17227.range);
          curmodule = (uu___111_17227.curmodule);
          gamma = (uu___111_17227.gamma);
          gamma_sig = (uu___111_17227.gamma_sig);
          gamma_cache = (uu___111_17227.gamma_cache);
          modules = (uu___111_17227.modules);
          expected_typ = (uu___111_17227.expected_typ);
          sigtab = (uu___111_17227.sigtab);
          is_pattern = (uu___111_17227.is_pattern);
          instantiate_imp = (uu___111_17227.instantiate_imp);
          effects = (uu___111_17227.effects);
          generalize = (uu___111_17227.generalize);
          letrecs = (uu___111_17227.letrecs);
          top_level = (uu___111_17227.top_level);
          check_uvars = (uu___111_17227.check_uvars);
          use_eq = (uu___111_17227.use_eq);
          is_iface = (uu___111_17227.is_iface);
          admit = (uu___111_17227.admit);
          lax = (uu___111_17227.lax);
          lax_universes = (uu___111_17227.lax_universes);
          failhard = (uu___111_17227.failhard);
          nosynth = (uu___111_17227.nosynth);
          tc_term = (uu___111_17227.tc_term);
          type_of = (uu___111_17227.type_of);
          universe_of = (uu___111_17227.universe_of);
          check_type_of = (uu___111_17227.check_type_of);
          use_bv_sorts = (uu___111_17227.use_bv_sorts);
          qtbl_name_and_index = (uu___111_17227.qtbl_name_and_index);
          normalized_eff_names = (uu___111_17227.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___111_17227.synth_hook);
          splice = (uu___111_17227.splice);
          is_native_tactic = (uu___111_17227.is_native_tactic);
          identifier_info = (uu___111_17227.identifier_info);
          tc_hooks = (uu___111_17227.tc_hooks);
          dsenv = (uu___111_17227.dsenv);
          dep_graph = (uu___111_17227.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___112_17267 = e  in
      {
        solver = (uu___112_17267.solver);
        range = (uu___112_17267.range);
        curmodule = (uu___112_17267.curmodule);
        gamma = (uu___112_17267.gamma);
        gamma_sig = (uu___112_17267.gamma_sig);
        gamma_cache = (uu___112_17267.gamma_cache);
        modules = (uu___112_17267.modules);
        expected_typ = (uu___112_17267.expected_typ);
        sigtab = (uu___112_17267.sigtab);
        is_pattern = (uu___112_17267.is_pattern);
        instantiate_imp = (uu___112_17267.instantiate_imp);
        effects = (uu___112_17267.effects);
        generalize = (uu___112_17267.generalize);
        letrecs = (uu___112_17267.letrecs);
        top_level = (uu___112_17267.top_level);
        check_uvars = (uu___112_17267.check_uvars);
        use_eq = (uu___112_17267.use_eq);
        is_iface = (uu___112_17267.is_iface);
        admit = (uu___112_17267.admit);
        lax = (uu___112_17267.lax);
        lax_universes = (uu___112_17267.lax_universes);
        failhard = (uu___112_17267.failhard);
        nosynth = (uu___112_17267.nosynth);
        tc_term = (uu___112_17267.tc_term);
        type_of = (uu___112_17267.type_of);
        universe_of = (uu___112_17267.universe_of);
        check_type_of = (uu___112_17267.check_type_of);
        use_bv_sorts = (uu___112_17267.use_bv_sorts);
        qtbl_name_and_index = (uu___112_17267.qtbl_name_and_index);
        normalized_eff_names = (uu___112_17267.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___112_17267.synth_hook);
        splice = (uu___112_17267.splice);
        is_native_tactic = (uu___112_17267.is_native_tactic);
        identifier_info = (uu___112_17267.identifier_info);
        tc_hooks = (uu___112_17267.tc_hooks);
        dsenv = (uu___112_17267.dsenv);
        dep_graph = (uu___112_17267.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____17282 = FStar_Syntax_Free.names t  in
      let uu____17285 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____17282 uu____17285
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____17306 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____17306
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17314 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____17314
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____17333 =
      match uu____17333 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____17349 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____17349)
       in
    let uu____17351 =
      let uu____17354 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____17354 FStar_List.rev  in
    FStar_All.pipe_right uu____17351 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____17369  -> ());
    push = (fun uu____17371  -> ());
    pop = (fun uu____17373  -> ());
    encode_modul = (fun uu____17376  -> fun uu____17377  -> ());
    encode_sig = (fun uu____17380  -> fun uu____17381  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____17387 =
             let uu____17394 = FStar_Options.peek ()  in (e, g, uu____17394)
              in
           [uu____17387]);
    solve = (fun uu____17410  -> fun uu____17411  -> fun uu____17412  -> ());
    finish = (fun uu____17418  -> ());
    refresh = (fun uu____17420  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___113_17426 = en  in
    let uu____17427 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____17430 = FStar_Util.smap_copy en.sigtab  in
    let uu____17433 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___113_17426.solver);
      range = (uu___113_17426.range);
      curmodule = (uu___113_17426.curmodule);
      gamma = (uu___113_17426.gamma);
      gamma_sig = (uu___113_17426.gamma_sig);
      gamma_cache = uu____17427;
      modules = (uu___113_17426.modules);
      expected_typ = (uu___113_17426.expected_typ);
      sigtab = uu____17430;
      is_pattern = (uu___113_17426.is_pattern);
      instantiate_imp = (uu___113_17426.instantiate_imp);
      effects = (uu___113_17426.effects);
      generalize = (uu___113_17426.generalize);
      letrecs = (uu___113_17426.letrecs);
      top_level = (uu___113_17426.top_level);
      check_uvars = (uu___113_17426.check_uvars);
      use_eq = (uu___113_17426.use_eq);
      is_iface = (uu___113_17426.is_iface);
      admit = (uu___113_17426.admit);
      lax = (uu___113_17426.lax);
      lax_universes = (uu___113_17426.lax_universes);
      failhard = (uu___113_17426.failhard);
      nosynth = (uu___113_17426.nosynth);
      tc_term = (uu___113_17426.tc_term);
      type_of = (uu___113_17426.type_of);
      universe_of = (uu___113_17426.universe_of);
      check_type_of = (uu___113_17426.check_type_of);
      use_bv_sorts = (uu___113_17426.use_bv_sorts);
      qtbl_name_and_index = (uu___113_17426.qtbl_name_and_index);
      normalized_eff_names = (uu___113_17426.normalized_eff_names);
      proof_ns = (uu___113_17426.proof_ns);
      synth_hook = (uu___113_17426.synth_hook);
      splice = (uu___113_17426.splice);
      is_native_tactic = (uu___113_17426.is_native_tactic);
      identifier_info = (uu___113_17426.identifier_info);
      tc_hooks = (uu___113_17426.tc_hooks);
      dsenv = uu____17433;
      dep_graph = (uu___113_17426.dep_graph)
    }
  