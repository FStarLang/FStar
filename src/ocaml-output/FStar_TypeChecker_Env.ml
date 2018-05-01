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
  
type solver_depth_t =
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                  show]
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
           (fun uu___100_8114  ->
              match uu___100_8114 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8117 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8117  in
                  let uu____8118 =
                    let uu____8119 = FStar_Syntax_Subst.compress y  in
                    uu____8119.FStar_Syntax_Syntax.n  in
                  (match uu____8118 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8123 =
                         let uu___114_8124 = y1  in
                         let uu____8125 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___114_8124.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___114_8124.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8125
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8123
                   | uu____8128 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___115_8140 = env  in
      let uu____8141 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___115_8140.solver);
        range = (uu___115_8140.range);
        curmodule = (uu___115_8140.curmodule);
        gamma = uu____8141;
        gamma_sig = (uu___115_8140.gamma_sig);
        gamma_cache = (uu___115_8140.gamma_cache);
        modules = (uu___115_8140.modules);
        expected_typ = (uu___115_8140.expected_typ);
        sigtab = (uu___115_8140.sigtab);
        is_pattern = (uu___115_8140.is_pattern);
        instantiate_imp = (uu___115_8140.instantiate_imp);
        effects = (uu___115_8140.effects);
        generalize = (uu___115_8140.generalize);
        letrecs = (uu___115_8140.letrecs);
        top_level = (uu___115_8140.top_level);
        check_uvars = (uu___115_8140.check_uvars);
        use_eq = (uu___115_8140.use_eq);
        is_iface = (uu___115_8140.is_iface);
        admit = (uu___115_8140.admit);
        lax = (uu___115_8140.lax);
        lax_universes = (uu___115_8140.lax_universes);
        failhard = (uu___115_8140.failhard);
        nosynth = (uu___115_8140.nosynth);
        tc_term = (uu___115_8140.tc_term);
        type_of = (uu___115_8140.type_of);
        universe_of = (uu___115_8140.universe_of);
        check_type_of = (uu___115_8140.check_type_of);
        use_bv_sorts = (uu___115_8140.use_bv_sorts);
        qtbl_name_and_index = (uu___115_8140.qtbl_name_and_index);
        normalized_eff_names = (uu___115_8140.normalized_eff_names);
        proof_ns = (uu___115_8140.proof_ns);
        synth_hook = (uu___115_8140.synth_hook);
        splice = (uu___115_8140.splice);
        is_native_tactic = (uu___115_8140.is_native_tactic);
        identifier_info = (uu___115_8140.identifier_info);
        tc_hooks = (uu___115_8140.tc_hooks);
        dsenv = (uu___115_8140.dsenv);
        dep_graph = (uu___115_8140.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8148  -> fun uu____8149  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___116_8169 = env  in
      {
        solver = (uu___116_8169.solver);
        range = (uu___116_8169.range);
        curmodule = (uu___116_8169.curmodule);
        gamma = (uu___116_8169.gamma);
        gamma_sig = (uu___116_8169.gamma_sig);
        gamma_cache = (uu___116_8169.gamma_cache);
        modules = (uu___116_8169.modules);
        expected_typ = (uu___116_8169.expected_typ);
        sigtab = (uu___116_8169.sigtab);
        is_pattern = (uu___116_8169.is_pattern);
        instantiate_imp = (uu___116_8169.instantiate_imp);
        effects = (uu___116_8169.effects);
        generalize = (uu___116_8169.generalize);
        letrecs = (uu___116_8169.letrecs);
        top_level = (uu___116_8169.top_level);
        check_uvars = (uu___116_8169.check_uvars);
        use_eq = (uu___116_8169.use_eq);
        is_iface = (uu___116_8169.is_iface);
        admit = (uu___116_8169.admit);
        lax = (uu___116_8169.lax);
        lax_universes = (uu___116_8169.lax_universes);
        failhard = (uu___116_8169.failhard);
        nosynth = (uu___116_8169.nosynth);
        tc_term = (uu___116_8169.tc_term);
        type_of = (uu___116_8169.type_of);
        universe_of = (uu___116_8169.universe_of);
        check_type_of = (uu___116_8169.check_type_of);
        use_bv_sorts = (uu___116_8169.use_bv_sorts);
        qtbl_name_and_index = (uu___116_8169.qtbl_name_and_index);
        normalized_eff_names = (uu___116_8169.normalized_eff_names);
        proof_ns = (uu___116_8169.proof_ns);
        synth_hook = (uu___116_8169.synth_hook);
        splice = (uu___116_8169.splice);
        is_native_tactic = (uu___116_8169.is_native_tactic);
        identifier_info = (uu___116_8169.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___116_8169.dsenv);
        dep_graph = (uu___116_8169.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___117_8180 = e  in
      {
        solver = (uu___117_8180.solver);
        range = (uu___117_8180.range);
        curmodule = (uu___117_8180.curmodule);
        gamma = (uu___117_8180.gamma);
        gamma_sig = (uu___117_8180.gamma_sig);
        gamma_cache = (uu___117_8180.gamma_cache);
        modules = (uu___117_8180.modules);
        expected_typ = (uu___117_8180.expected_typ);
        sigtab = (uu___117_8180.sigtab);
        is_pattern = (uu___117_8180.is_pattern);
        instantiate_imp = (uu___117_8180.instantiate_imp);
        effects = (uu___117_8180.effects);
        generalize = (uu___117_8180.generalize);
        letrecs = (uu___117_8180.letrecs);
        top_level = (uu___117_8180.top_level);
        check_uvars = (uu___117_8180.check_uvars);
        use_eq = (uu___117_8180.use_eq);
        is_iface = (uu___117_8180.is_iface);
        admit = (uu___117_8180.admit);
        lax = (uu___117_8180.lax);
        lax_universes = (uu___117_8180.lax_universes);
        failhard = (uu___117_8180.failhard);
        nosynth = (uu___117_8180.nosynth);
        tc_term = (uu___117_8180.tc_term);
        type_of = (uu___117_8180.type_of);
        universe_of = (uu___117_8180.universe_of);
        check_type_of = (uu___117_8180.check_type_of);
        use_bv_sorts = (uu___117_8180.use_bv_sorts);
        qtbl_name_and_index = (uu___117_8180.qtbl_name_and_index);
        normalized_eff_names = (uu___117_8180.normalized_eff_names);
        proof_ns = (uu___117_8180.proof_ns);
        synth_hook = (uu___117_8180.synth_hook);
        splice = (uu___117_8180.splice);
        is_native_tactic = (uu___117_8180.is_native_tactic);
        identifier_info = (uu___117_8180.identifier_info);
        tc_hooks = (uu___117_8180.tc_hooks);
        dsenv = (uu___117_8180.dsenv);
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
      | (NoDelta ,uu____8203) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8204,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8205,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8206 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8215 . unit -> 'Auu____8215 FStar_Util.smap =
  fun uu____8222  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8227 . unit -> 'Auu____8227 FStar_Util.smap =
  fun uu____8234  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8344 = new_gamma_cache ()  in
                let uu____8347 = new_sigtab ()  in
                let uu____8350 =
                  let uu____8363 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8363, FStar_Pervasives_Native.None)  in
                let uu____8378 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8381 = FStar_Options.using_facts_from ()  in
                let uu____8382 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8385 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____8344;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8347;
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
                  qtbl_name_and_index = uu____8350;
                  normalized_eff_names = uu____8378;
                  proof_ns = uu____8381;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8421  -> false);
                  identifier_info = uu____8382;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8385;
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
  fun uu____8512  ->
    let uu____8513 = FStar_ST.op_Bang query_indices  in
    match uu____8513 with
    | [] -> failwith "Empty query indices!"
    | uu____8567 ->
        let uu____8576 =
          let uu____8585 =
            let uu____8592 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8592  in
          let uu____8646 = FStar_ST.op_Bang query_indices  in uu____8585 ::
            uu____8646
           in
        FStar_ST.op_Colon_Equals query_indices uu____8576
  
let (pop_query_indices : unit -> unit) =
  fun uu____8743  ->
    let uu____8744 = FStar_ST.op_Bang query_indices  in
    match uu____8744 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____8867  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8897  ->
    match uu____8897 with
    | (l,n1) ->
        let uu____8904 = FStar_ST.op_Bang query_indices  in
        (match uu____8904 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9023 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9042  ->
    let uu____9043 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9043
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9120 =
       let uu____9123 = FStar_ST.op_Bang stack  in env :: uu____9123  in
     FStar_ST.op_Colon_Equals stack uu____9120);
    (let uu___118_9180 = env  in
     let uu____9181 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9184 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9187 =
       let uu____9200 =
         let uu____9203 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9203  in
       let uu____9228 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9200, uu____9228)  in
     let uu____9269 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9272 =
       let uu____9275 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9275  in
     {
       solver = (uu___118_9180.solver);
       range = (uu___118_9180.range);
       curmodule = (uu___118_9180.curmodule);
       gamma = (uu___118_9180.gamma);
       gamma_sig = (uu___118_9180.gamma_sig);
       gamma_cache = uu____9181;
       modules = (uu___118_9180.modules);
       expected_typ = (uu___118_9180.expected_typ);
       sigtab = uu____9184;
       is_pattern = (uu___118_9180.is_pattern);
       instantiate_imp = (uu___118_9180.instantiate_imp);
       effects = (uu___118_9180.effects);
       generalize = (uu___118_9180.generalize);
       letrecs = (uu___118_9180.letrecs);
       top_level = (uu___118_9180.top_level);
       check_uvars = (uu___118_9180.check_uvars);
       use_eq = (uu___118_9180.use_eq);
       is_iface = (uu___118_9180.is_iface);
       admit = (uu___118_9180.admit);
       lax = (uu___118_9180.lax);
       lax_universes = (uu___118_9180.lax_universes);
       failhard = (uu___118_9180.failhard);
       nosynth = (uu___118_9180.nosynth);
       tc_term = (uu___118_9180.tc_term);
       type_of = (uu___118_9180.type_of);
       universe_of = (uu___118_9180.universe_of);
       check_type_of = (uu___118_9180.check_type_of);
       use_bv_sorts = (uu___118_9180.use_bv_sorts);
       qtbl_name_and_index = uu____9187;
       normalized_eff_names = uu____9269;
       proof_ns = (uu___118_9180.proof_ns);
       synth_hook = (uu___118_9180.synth_hook);
       splice = (uu___118_9180.splice);
       is_native_tactic = (uu___118_9180.is_native_tactic);
       identifier_info = uu____9272;
       tc_hooks = (uu___118_9180.tc_hooks);
       dsenv = (uu___118_9180.dsenv);
       dep_graph = (uu___118_9180.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9325  ->
    let uu____9326 = FStar_ST.op_Bang stack  in
    match uu____9326 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9388 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____9460  ->
           let uu____9461 = snapshot_stack env  in
           match uu____9461 with
           | (stack_depth,env1) ->
               let uu____9486 = snapshot_query_indices ()  in
               (match uu____9486 with
                | (query_indices_depth,()) ->
                    let uu____9510 = (env1.solver).snapshot msg  in
                    (match uu____9510 with
                     | (solver_depth,()) ->
                         let uu____9552 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9552 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___119_9598 = env1  in
                                 {
                                   solver = (uu___119_9598.solver);
                                   range = (uu___119_9598.range);
                                   curmodule = (uu___119_9598.curmodule);
                                   gamma = (uu___119_9598.gamma);
                                   gamma_sig = (uu___119_9598.gamma_sig);
                                   gamma_cache = (uu___119_9598.gamma_cache);
                                   modules = (uu___119_9598.modules);
                                   expected_typ =
                                     (uu___119_9598.expected_typ);
                                   sigtab = (uu___119_9598.sigtab);
                                   is_pattern = (uu___119_9598.is_pattern);
                                   instantiate_imp =
                                     (uu___119_9598.instantiate_imp);
                                   effects = (uu___119_9598.effects);
                                   generalize = (uu___119_9598.generalize);
                                   letrecs = (uu___119_9598.letrecs);
                                   top_level = (uu___119_9598.top_level);
                                   check_uvars = (uu___119_9598.check_uvars);
                                   use_eq = (uu___119_9598.use_eq);
                                   is_iface = (uu___119_9598.is_iface);
                                   admit = (uu___119_9598.admit);
                                   lax = (uu___119_9598.lax);
                                   lax_universes =
                                     (uu___119_9598.lax_universes);
                                   failhard = (uu___119_9598.failhard);
                                   nosynth = (uu___119_9598.nosynth);
                                   tc_term = (uu___119_9598.tc_term);
                                   type_of = (uu___119_9598.type_of);
                                   universe_of = (uu___119_9598.universe_of);
                                   check_type_of =
                                     (uu___119_9598.check_type_of);
                                   use_bv_sorts =
                                     (uu___119_9598.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___119_9598.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___119_9598.normalized_eff_names);
                                   proof_ns = (uu___119_9598.proof_ns);
                                   synth_hook = (uu___119_9598.synth_hook);
                                   splice = (uu___119_9598.splice);
                                   is_native_tactic =
                                     (uu___119_9598.is_native_tactic);
                                   identifier_info =
                                     (uu___119_9598.identifier_info);
                                   tc_hooks = (uu___119_9598.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___119_9598.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9629  ->
             let uu____9630 =
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
             match uu____9630 with
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
                             ((let uu____9708 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9708
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9719 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9719
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9746,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9778 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9804  ->
                  match uu____9804 with
                  | (m,uu____9810) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9778 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___120_9818 = env  in
               {
                 solver = (uu___120_9818.solver);
                 range = (uu___120_9818.range);
                 curmodule = (uu___120_9818.curmodule);
                 gamma = (uu___120_9818.gamma);
                 gamma_sig = (uu___120_9818.gamma_sig);
                 gamma_cache = (uu___120_9818.gamma_cache);
                 modules = (uu___120_9818.modules);
                 expected_typ = (uu___120_9818.expected_typ);
                 sigtab = (uu___120_9818.sigtab);
                 is_pattern = (uu___120_9818.is_pattern);
                 instantiate_imp = (uu___120_9818.instantiate_imp);
                 effects = (uu___120_9818.effects);
                 generalize = (uu___120_9818.generalize);
                 letrecs = (uu___120_9818.letrecs);
                 top_level = (uu___120_9818.top_level);
                 check_uvars = (uu___120_9818.check_uvars);
                 use_eq = (uu___120_9818.use_eq);
                 is_iface = (uu___120_9818.is_iface);
                 admit = (uu___120_9818.admit);
                 lax = (uu___120_9818.lax);
                 lax_universes = (uu___120_9818.lax_universes);
                 failhard = (uu___120_9818.failhard);
                 nosynth = (uu___120_9818.nosynth);
                 tc_term = (uu___120_9818.tc_term);
                 type_of = (uu___120_9818.type_of);
                 universe_of = (uu___120_9818.universe_of);
                 check_type_of = (uu___120_9818.check_type_of);
                 use_bv_sorts = (uu___120_9818.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___120_9818.normalized_eff_names);
                 proof_ns = (uu___120_9818.proof_ns);
                 synth_hook = (uu___120_9818.synth_hook);
                 splice = (uu___120_9818.splice);
                 is_native_tactic = (uu___120_9818.is_native_tactic);
                 identifier_info = (uu___120_9818.identifier_info);
                 tc_hooks = (uu___120_9818.tc_hooks);
                 dsenv = (uu___120_9818.dsenv);
                 dep_graph = (uu___120_9818.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9831,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___121_9840 = env  in
               {
                 solver = (uu___121_9840.solver);
                 range = (uu___121_9840.range);
                 curmodule = (uu___121_9840.curmodule);
                 gamma = (uu___121_9840.gamma);
                 gamma_sig = (uu___121_9840.gamma_sig);
                 gamma_cache = (uu___121_9840.gamma_cache);
                 modules = (uu___121_9840.modules);
                 expected_typ = (uu___121_9840.expected_typ);
                 sigtab = (uu___121_9840.sigtab);
                 is_pattern = (uu___121_9840.is_pattern);
                 instantiate_imp = (uu___121_9840.instantiate_imp);
                 effects = (uu___121_9840.effects);
                 generalize = (uu___121_9840.generalize);
                 letrecs = (uu___121_9840.letrecs);
                 top_level = (uu___121_9840.top_level);
                 check_uvars = (uu___121_9840.check_uvars);
                 use_eq = (uu___121_9840.use_eq);
                 is_iface = (uu___121_9840.is_iface);
                 admit = (uu___121_9840.admit);
                 lax = (uu___121_9840.lax);
                 lax_universes = (uu___121_9840.lax_universes);
                 failhard = (uu___121_9840.failhard);
                 nosynth = (uu___121_9840.nosynth);
                 tc_term = (uu___121_9840.tc_term);
                 type_of = (uu___121_9840.type_of);
                 universe_of = (uu___121_9840.universe_of);
                 check_type_of = (uu___121_9840.check_type_of);
                 use_bv_sorts = (uu___121_9840.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___121_9840.normalized_eff_names);
                 proof_ns = (uu___121_9840.proof_ns);
                 synth_hook = (uu___121_9840.synth_hook);
                 splice = (uu___121_9840.splice);
                 is_native_tactic = (uu___121_9840.is_native_tactic);
                 identifier_info = (uu___121_9840.identifier_info);
                 tc_hooks = (uu___121_9840.tc_hooks);
                 dsenv = (uu___121_9840.dsenv);
                 dep_graph = (uu___121_9840.dep_graph)
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
        (let uu___122_9874 = e  in
         {
           solver = (uu___122_9874.solver);
           range = r;
           curmodule = (uu___122_9874.curmodule);
           gamma = (uu___122_9874.gamma);
           gamma_sig = (uu___122_9874.gamma_sig);
           gamma_cache = (uu___122_9874.gamma_cache);
           modules = (uu___122_9874.modules);
           expected_typ = (uu___122_9874.expected_typ);
           sigtab = (uu___122_9874.sigtab);
           is_pattern = (uu___122_9874.is_pattern);
           instantiate_imp = (uu___122_9874.instantiate_imp);
           effects = (uu___122_9874.effects);
           generalize = (uu___122_9874.generalize);
           letrecs = (uu___122_9874.letrecs);
           top_level = (uu___122_9874.top_level);
           check_uvars = (uu___122_9874.check_uvars);
           use_eq = (uu___122_9874.use_eq);
           is_iface = (uu___122_9874.is_iface);
           admit = (uu___122_9874.admit);
           lax = (uu___122_9874.lax);
           lax_universes = (uu___122_9874.lax_universes);
           failhard = (uu___122_9874.failhard);
           nosynth = (uu___122_9874.nosynth);
           tc_term = (uu___122_9874.tc_term);
           type_of = (uu___122_9874.type_of);
           universe_of = (uu___122_9874.universe_of);
           check_type_of = (uu___122_9874.check_type_of);
           use_bv_sorts = (uu___122_9874.use_bv_sorts);
           qtbl_name_and_index = (uu___122_9874.qtbl_name_and_index);
           normalized_eff_names = (uu___122_9874.normalized_eff_names);
           proof_ns = (uu___122_9874.proof_ns);
           synth_hook = (uu___122_9874.synth_hook);
           splice = (uu___122_9874.splice);
           is_native_tactic = (uu___122_9874.is_native_tactic);
           identifier_info = (uu___122_9874.identifier_info);
           tc_hooks = (uu___122_9874.tc_hooks);
           dsenv = (uu___122_9874.dsenv);
           dep_graph = (uu___122_9874.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____9890 =
        let uu____9891 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____9891 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9890
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____9953 =
          let uu____9954 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____9954 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9953
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10016 =
          let uu____10017 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10017 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10016
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10079 =
        let uu____10080 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10080 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10079
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___123_10149 = env  in
      {
        solver = (uu___123_10149.solver);
        range = (uu___123_10149.range);
        curmodule = lid;
        gamma = (uu___123_10149.gamma);
        gamma_sig = (uu___123_10149.gamma_sig);
        gamma_cache = (uu___123_10149.gamma_cache);
        modules = (uu___123_10149.modules);
        expected_typ = (uu___123_10149.expected_typ);
        sigtab = (uu___123_10149.sigtab);
        is_pattern = (uu___123_10149.is_pattern);
        instantiate_imp = (uu___123_10149.instantiate_imp);
        effects = (uu___123_10149.effects);
        generalize = (uu___123_10149.generalize);
        letrecs = (uu___123_10149.letrecs);
        top_level = (uu___123_10149.top_level);
        check_uvars = (uu___123_10149.check_uvars);
        use_eq = (uu___123_10149.use_eq);
        is_iface = (uu___123_10149.is_iface);
        admit = (uu___123_10149.admit);
        lax = (uu___123_10149.lax);
        lax_universes = (uu___123_10149.lax_universes);
        failhard = (uu___123_10149.failhard);
        nosynth = (uu___123_10149.nosynth);
        tc_term = (uu___123_10149.tc_term);
        type_of = (uu___123_10149.type_of);
        universe_of = (uu___123_10149.universe_of);
        check_type_of = (uu___123_10149.check_type_of);
        use_bv_sorts = (uu___123_10149.use_bv_sorts);
        qtbl_name_and_index = (uu___123_10149.qtbl_name_and_index);
        normalized_eff_names = (uu___123_10149.normalized_eff_names);
        proof_ns = (uu___123_10149.proof_ns);
        synth_hook = (uu___123_10149.synth_hook);
        splice = (uu___123_10149.splice);
        is_native_tactic = (uu___123_10149.is_native_tactic);
        identifier_info = (uu___123_10149.identifier_info);
        tc_hooks = (uu___123_10149.tc_hooks);
        dsenv = (uu___123_10149.dsenv);
        dep_graph = (uu___123_10149.dep_graph)
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
      let uu____10176 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10176
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10186 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10186)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10196 =
      let uu____10197 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10197  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10196)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10202  ->
    let uu____10203 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10203
  
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
      | ((formals,t),uu____10259) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10293 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10293)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___101_10309  ->
    match uu___101_10309 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10335  -> new_u_univ ()))
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
      let uu____10354 = inst_tscheme t  in
      match uu____10354 with
      | (us,t1) ->
          let uu____10365 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10365)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10385  ->
          match uu____10385 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10404 =
                         let uu____10405 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10406 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10407 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10408 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10405 uu____10406 uu____10407 uu____10408
                          in
                       failwith uu____10404)
                    else ();
                    (let uu____10410 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10410))
               | uu____10419 ->
                   let uu____10420 =
                     let uu____10421 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10421
                      in
                   failwith uu____10420)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10427 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10433 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10439 -> false
  
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
             | ([],uu____10481) -> Maybe
             | (uu____10488,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10507 -> No  in
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
          let uu____10598 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10598 with
          | FStar_Pervasives_Native.None  ->
              let uu____10621 =
                FStar_Util.find_map env.gamma
                  (fun uu___102_10665  ->
                     match uu___102_10665 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____10704 = FStar_Ident.lid_equals lid l  in
                         if uu____10704
                         then
                           let uu____10725 =
                             let uu____10744 =
                               let uu____10759 = inst_tscheme t  in
                               FStar_Util.Inl uu____10759  in
                             let uu____10774 = FStar_Ident.range_of_lid l  in
                             (uu____10744, uu____10774)  in
                           FStar_Pervasives_Native.Some uu____10725
                         else FStar_Pervasives_Native.None
                     | uu____10826 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____10621
                (fun uu____10864  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___103_10873  ->
                        match uu___103_10873 with
                        | (uu____10876,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____10878);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____10879;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____10880;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____10881;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____10882;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____10902 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____10902
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
                                  uu____10950 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____10957 -> cache t  in
                            let uu____10958 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____10958 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____10964 =
                                   let uu____10965 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____10965)
                                    in
                                 maybe_cache uu____10964)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11033 = find_in_sigtab env lid  in
         match uu____11033 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11120) ->
          add_sigelts env ses
      | uu____11129 ->
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
            | uu____11143 -> ()))

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
        (fun uu___104_11174  ->
           match uu___104_11174 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11192 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11253,lb::[]),uu____11255) ->
            let uu____11262 =
              let uu____11271 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11280 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11271, uu____11280)  in
            FStar_Pervasives_Native.Some uu____11262
        | FStar_Syntax_Syntax.Sig_let ((uu____11293,lbs),uu____11295) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11325 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11337 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11337
                     then
                       let uu____11348 =
                         let uu____11357 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11366 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11357, uu____11366)  in
                       FStar_Pervasives_Native.Some uu____11348
                     else FStar_Pervasives_Native.None)
        | uu____11388 -> FStar_Pervasives_Native.None
  
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
          let uu____11447 =
            let uu____11456 =
              let uu____11461 =
                let uu____11462 =
                  let uu____11465 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11465
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11462)  in
              inst_tscheme1 uu____11461  in
            (uu____11456, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11447
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11487,uu____11488) ->
          let uu____11493 =
            let uu____11502 =
              let uu____11507 =
                let uu____11508 =
                  let uu____11511 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11511  in
                (us, uu____11508)  in
              inst_tscheme1 uu____11507  in
            (uu____11502, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11493
      | uu____11530 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11618 =
          match uu____11618 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11714,uvs,t,uu____11717,uu____11718,uu____11719);
                      FStar_Syntax_Syntax.sigrng = uu____11720;
                      FStar_Syntax_Syntax.sigquals = uu____11721;
                      FStar_Syntax_Syntax.sigmeta = uu____11722;
                      FStar_Syntax_Syntax.sigattrs = uu____11723;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11744 =
                     let uu____11753 = inst_tscheme1 (uvs, t)  in
                     (uu____11753, rng)  in
                   FStar_Pervasives_Native.Some uu____11744
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11777;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11779;
                      FStar_Syntax_Syntax.sigattrs = uu____11780;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11797 =
                     let uu____11798 = in_cur_mod env l  in uu____11798 = Yes
                      in
                   if uu____11797
                   then
                     let uu____11809 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____11809
                      then
                        let uu____11822 =
                          let uu____11831 = inst_tscheme1 (uvs, t)  in
                          (uu____11831, rng)  in
                        FStar_Pervasives_Native.Some uu____11822
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____11862 =
                        let uu____11871 = inst_tscheme1 (uvs, t)  in
                        (uu____11871, rng)  in
                      FStar_Pervasives_Native.Some uu____11862)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11896,uu____11897);
                      FStar_Syntax_Syntax.sigrng = uu____11898;
                      FStar_Syntax_Syntax.sigquals = uu____11899;
                      FStar_Syntax_Syntax.sigmeta = uu____11900;
                      FStar_Syntax_Syntax.sigattrs = uu____11901;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____11940 =
                          let uu____11949 = inst_tscheme1 (uvs, k)  in
                          (uu____11949, rng)  in
                        FStar_Pervasives_Native.Some uu____11940
                    | uu____11970 ->
                        let uu____11971 =
                          let uu____11980 =
                            let uu____11985 =
                              let uu____11986 =
                                let uu____11989 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11989
                                 in
                              (uvs, uu____11986)  in
                            inst_tscheme1 uu____11985  in
                          (uu____11980, rng)  in
                        FStar_Pervasives_Native.Some uu____11971)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12012,uu____12013);
                      FStar_Syntax_Syntax.sigrng = uu____12014;
                      FStar_Syntax_Syntax.sigquals = uu____12015;
                      FStar_Syntax_Syntax.sigmeta = uu____12016;
                      FStar_Syntax_Syntax.sigattrs = uu____12017;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12057 =
                          let uu____12066 = inst_tscheme_with (uvs, k) us  in
                          (uu____12066, rng)  in
                        FStar_Pervasives_Native.Some uu____12057
                    | uu____12087 ->
                        let uu____12088 =
                          let uu____12097 =
                            let uu____12102 =
                              let uu____12103 =
                                let uu____12106 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12106
                                 in
                              (uvs, uu____12103)  in
                            inst_tscheme_with uu____12102 us  in
                          (uu____12097, rng)  in
                        FStar_Pervasives_Native.Some uu____12088)
               | FStar_Util.Inr se ->
                   let uu____12142 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12163;
                          FStar_Syntax_Syntax.sigrng = uu____12164;
                          FStar_Syntax_Syntax.sigquals = uu____12165;
                          FStar_Syntax_Syntax.sigmeta = uu____12166;
                          FStar_Syntax_Syntax.sigattrs = uu____12167;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12182 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12142
                     (FStar_Util.map_option
                        (fun uu____12230  ->
                           match uu____12230 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12261 =
          let uu____12272 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12272 mapper  in
        match uu____12261 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12346 =
              let uu____12357 =
                let uu____12364 =
                  let uu___124_12367 = t  in
                  let uu____12368 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___124_12367.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12368;
                    FStar_Syntax_Syntax.vars =
                      (uu___124_12367.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12364)  in
              (uu____12357, r)  in
            FStar_Pervasives_Native.Some uu____12346
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12415 = lookup_qname env l  in
      match uu____12415 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12434 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12486 = try_lookup_bv env bv  in
      match uu____12486 with
      | FStar_Pervasives_Native.None  ->
          let uu____12501 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12501 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12516 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12517 =
            let uu____12518 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12518  in
          (uu____12516, uu____12517)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12539 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12539 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12605 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12605  in
          let uu____12606 =
            let uu____12615 =
              let uu____12620 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12620)  in
            (uu____12615, r1)  in
          FStar_Pervasives_Native.Some uu____12606
  
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
        let uu____12654 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12654 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12687,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12712 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12712  in
            let uu____12713 =
              let uu____12718 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12718, r1)  in
            FStar_Pervasives_Native.Some uu____12713
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12741 = try_lookup_lid env l  in
      match uu____12741 with
      | FStar_Pervasives_Native.None  ->
          let uu____12768 = name_not_found l  in
          let uu____12773 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12768 uu____12773
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___105_12813  ->
              match uu___105_12813 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12815 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12834 = lookup_qname env lid  in
      match uu____12834 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12843,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12846;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12848;
              FStar_Syntax_Syntax.sigattrs = uu____12849;_},FStar_Pervasives_Native.None
            ),uu____12850)
          ->
          let uu____12899 =
            let uu____12906 =
              let uu____12907 =
                let uu____12910 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____12910 t  in
              (uvs, uu____12907)  in
            (uu____12906, q)  in
          FStar_Pervasives_Native.Some uu____12899
      | uu____12923 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12944 = lookup_qname env lid  in
      match uu____12944 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12949,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12952;
              FStar_Syntax_Syntax.sigquals = uu____12953;
              FStar_Syntax_Syntax.sigmeta = uu____12954;
              FStar_Syntax_Syntax.sigattrs = uu____12955;_},FStar_Pervasives_Native.None
            ),uu____12956)
          ->
          let uu____13005 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13005 (uvs, t)
      | uu____13010 ->
          let uu____13011 = name_not_found lid  in
          let uu____13016 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13011 uu____13016
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13035 = lookup_qname env lid  in
      match uu____13035 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13040,uvs,t,uu____13043,uu____13044,uu____13045);
              FStar_Syntax_Syntax.sigrng = uu____13046;
              FStar_Syntax_Syntax.sigquals = uu____13047;
              FStar_Syntax_Syntax.sigmeta = uu____13048;
              FStar_Syntax_Syntax.sigattrs = uu____13049;_},FStar_Pervasives_Native.None
            ),uu____13050)
          ->
          let uu____13103 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13103 (uvs, t)
      | uu____13108 ->
          let uu____13109 = name_not_found lid  in
          let uu____13114 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13109 uu____13114
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13135 = lookup_qname env lid  in
      match uu____13135 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13142,uu____13143,uu____13144,uu____13145,uu____13146,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13148;
              FStar_Syntax_Syntax.sigquals = uu____13149;
              FStar_Syntax_Syntax.sigmeta = uu____13150;
              FStar_Syntax_Syntax.sigattrs = uu____13151;_},uu____13152),uu____13153)
          -> (true, dcs)
      | uu____13214 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13227 = lookup_qname env lid  in
      match uu____13227 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13228,uu____13229,uu____13230,l,uu____13232,uu____13233);
              FStar_Syntax_Syntax.sigrng = uu____13234;
              FStar_Syntax_Syntax.sigquals = uu____13235;
              FStar_Syntax_Syntax.sigmeta = uu____13236;
              FStar_Syntax_Syntax.sigattrs = uu____13237;_},uu____13238),uu____13239)
          -> l
      | uu____13294 ->
          let uu____13295 =
            let uu____13296 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13296  in
          failwith uu____13295
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13345)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13396,lbs),uu____13398)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13420 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13420
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13452 -> FStar_Pervasives_Native.None)
        | uu____13457 -> FStar_Pervasives_Native.None
  
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
        let uu____13487 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13487
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13512),uu____13513) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13562 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13583 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13583
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13602 = lookup_qname env ftv  in
      match uu____13602 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13606) ->
          let uu____13651 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13651 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13672,t),r) ->
               let uu____13687 =
                 let uu____13688 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13688 t  in
               FStar_Pervasives_Native.Some uu____13687)
      | uu____13689 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13700 = try_lookup_effect_lid env ftv  in
      match uu____13700 with
      | FStar_Pervasives_Native.None  ->
          let uu____13703 = name_not_found ftv  in
          let uu____13708 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13703 uu____13708
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
        let uu____13731 = lookup_qname env lid0  in
        match uu____13731 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13742);
                FStar_Syntax_Syntax.sigrng = uu____13743;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13745;
                FStar_Syntax_Syntax.sigattrs = uu____13746;_},FStar_Pervasives_Native.None
              ),uu____13747)
            ->
            let lid1 =
              let uu____13801 =
                let uu____13802 = FStar_Ident.range_of_lid lid  in
                let uu____13803 =
                  let uu____13804 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____13804  in
                FStar_Range.set_use_range uu____13802 uu____13803  in
              FStar_Ident.set_lid_range lid uu____13801  in
            let uu____13805 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___106_13809  ->
                      match uu___106_13809 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13810 -> false))
               in
            if uu____13805
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13824 =
                      let uu____13825 =
                        let uu____13826 = get_range env  in
                        FStar_Range.string_of_range uu____13826  in
                      let uu____13827 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____13828 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13825 uu____13827 uu____13828
                       in
                    failwith uu____13824)
                  in
               match (binders, univs1) with
               | ([],uu____13843) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____13864,uu____13865::uu____13866::uu____13867) ->
                   let uu____13884 =
                     let uu____13885 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____13886 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____13885 uu____13886
                      in
                   failwith uu____13884
               | uu____13893 ->
                   let uu____13906 =
                     let uu____13911 =
                       let uu____13912 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____13912)  in
                     inst_tscheme_with uu____13911 insts  in
                   (match uu____13906 with
                    | (uu____13925,t) ->
                        let t1 =
                          let uu____13928 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____13928 t  in
                        let uu____13929 =
                          let uu____13930 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13930.FStar_Syntax_Syntax.n  in
                        (match uu____13929 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____13961 -> failwith "Impossible")))
        | uu____13968 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____13991 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____13991 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14004,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14011 = find1 l2  in
            (match uu____14011 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14018 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14018 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14022 = find1 l  in
            (match uu____14022 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14027 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14027
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14041 = lookup_qname env l1  in
      match uu____14041 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14044;
              FStar_Syntax_Syntax.sigrng = uu____14045;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14047;
              FStar_Syntax_Syntax.sigattrs = uu____14048;_},uu____14049),uu____14050)
          -> q
      | uu____14101 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14122 =
          let uu____14123 =
            let uu____14124 = FStar_Util.string_of_int i  in
            let uu____14125 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14124 uu____14125
             in
          failwith uu____14123  in
        let uu____14126 = lookup_datacon env lid  in
        match uu____14126 with
        | (uu____14131,t) ->
            let uu____14133 =
              let uu____14134 = FStar_Syntax_Subst.compress t  in
              uu____14134.FStar_Syntax_Syntax.n  in
            (match uu____14133 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14138) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14169 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14169
                      FStar_Pervasives_Native.fst)
             | uu____14178 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14189 = lookup_qname env l  in
      match uu____14189 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14190,uu____14191,uu____14192);
              FStar_Syntax_Syntax.sigrng = uu____14193;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14195;
              FStar_Syntax_Syntax.sigattrs = uu____14196;_},uu____14197),uu____14198)
          ->
          FStar_Util.for_some
            (fun uu___107_14251  ->
               match uu___107_14251 with
               | FStar_Syntax_Syntax.Projector uu____14252 -> true
               | uu____14257 -> false) quals
      | uu____14258 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14269 = lookup_qname env lid  in
      match uu____14269 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14270,uu____14271,uu____14272,uu____14273,uu____14274,uu____14275);
              FStar_Syntax_Syntax.sigrng = uu____14276;
              FStar_Syntax_Syntax.sigquals = uu____14277;
              FStar_Syntax_Syntax.sigmeta = uu____14278;
              FStar_Syntax_Syntax.sigattrs = uu____14279;_},uu____14280),uu____14281)
          -> true
      | uu____14336 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14347 = lookup_qname env lid  in
      match uu____14347 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14348,uu____14349,uu____14350,uu____14351,uu____14352,uu____14353);
              FStar_Syntax_Syntax.sigrng = uu____14354;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14356;
              FStar_Syntax_Syntax.sigattrs = uu____14357;_},uu____14358),uu____14359)
          ->
          FStar_Util.for_some
            (fun uu___108_14420  ->
               match uu___108_14420 with
               | FStar_Syntax_Syntax.RecordType uu____14421 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14430 -> true
               | uu____14439 -> false) quals
      | uu____14440 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14446,uu____14447);
            FStar_Syntax_Syntax.sigrng = uu____14448;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14450;
            FStar_Syntax_Syntax.sigattrs = uu____14451;_},uu____14452),uu____14453)
        ->
        FStar_Util.for_some
          (fun uu___109_14510  ->
             match uu___109_14510 with
             | FStar_Syntax_Syntax.Action uu____14511 -> true
             | uu____14512 -> false) quals
    | uu____14513 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14524 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14524
  
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
      let uu____14538 =
        let uu____14539 = FStar_Syntax_Util.un_uinst head1  in
        uu____14539.FStar_Syntax_Syntax.n  in
      match uu____14538 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14543 ->
               true
           | uu____14544 -> false)
      | uu____14545 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14556 = lookup_qname env l  in
      match uu____14556 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14558),uu____14559) ->
          FStar_Util.for_some
            (fun uu___110_14607  ->
               match uu___110_14607 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14608 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14609 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14680 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14696) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14713 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14720 ->
                 FStar_Pervasives_Native.Some true
             | uu____14737 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14738 =
        let uu____14741 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14741 mapper  in
      match uu____14738 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14791 = lookup_qname env lid  in
      match uu____14791 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14792,uu____14793,tps,uu____14795,uu____14796,uu____14797);
              FStar_Syntax_Syntax.sigrng = uu____14798;
              FStar_Syntax_Syntax.sigquals = uu____14799;
              FStar_Syntax_Syntax.sigmeta = uu____14800;
              FStar_Syntax_Syntax.sigattrs = uu____14801;_},uu____14802),uu____14803)
          -> FStar_List.length tps
      | uu____14866 ->
          let uu____14867 = name_not_found lid  in
          let uu____14872 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14867 uu____14872
  
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
           (fun uu____14916  ->
              match uu____14916 with
              | (d,uu____14924) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____14939 = effect_decl_opt env l  in
      match uu____14939 with
      | FStar_Pervasives_Native.None  ->
          let uu____14954 = name_not_found l  in
          let uu____14959 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14954 uu____14959
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____14981  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15000  ->
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
        let uu____15031 = FStar_Ident.lid_equals l1 l2  in
        if uu____15031
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15039 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15039
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15047 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15100  ->
                        match uu____15100 with
                        | (m1,m2,uu____15113,uu____15114,uu____15115) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15047 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15132 =
                    let uu____15137 =
                      let uu____15138 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15139 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15138
                        uu____15139
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15137)
                     in
                  FStar_Errors.raise_error uu____15132 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15146,uu____15147,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15180 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15180
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
  'Auu____15196 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15196)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15225 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15251  ->
                match uu____15251 with
                | (d,uu____15257) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15225 with
      | FStar_Pervasives_Native.None  ->
          let uu____15268 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15268
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15281 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15281 with
           | (uu____15296,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15312)::(wp,uu____15314)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15350 -> failwith "Impossible"))
  
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
          let uu____15403 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15403
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15405 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15405
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
                  let uu____15413 = get_range env  in
                  let uu____15414 =
                    let uu____15421 =
                      let uu____15422 =
                        let uu____15437 =
                          let uu____15446 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15446]  in
                        (null_wp, uu____15437)  in
                      FStar_Syntax_Syntax.Tm_app uu____15422  in
                    FStar_Syntax_Syntax.mk uu____15421  in
                  uu____15414 FStar_Pervasives_Native.None uu____15413  in
                let uu____15478 =
                  let uu____15479 =
                    let uu____15488 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15488]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15479;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15478))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___125_15519 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___125_15519.order);
              joins = (uu___125_15519.joins)
            }  in
          let uu___126_15528 = env  in
          {
            solver = (uu___126_15528.solver);
            range = (uu___126_15528.range);
            curmodule = (uu___126_15528.curmodule);
            gamma = (uu___126_15528.gamma);
            gamma_sig = (uu___126_15528.gamma_sig);
            gamma_cache = (uu___126_15528.gamma_cache);
            modules = (uu___126_15528.modules);
            expected_typ = (uu___126_15528.expected_typ);
            sigtab = (uu___126_15528.sigtab);
            is_pattern = (uu___126_15528.is_pattern);
            instantiate_imp = (uu___126_15528.instantiate_imp);
            effects;
            generalize = (uu___126_15528.generalize);
            letrecs = (uu___126_15528.letrecs);
            top_level = (uu___126_15528.top_level);
            check_uvars = (uu___126_15528.check_uvars);
            use_eq = (uu___126_15528.use_eq);
            is_iface = (uu___126_15528.is_iface);
            admit = (uu___126_15528.admit);
            lax = (uu___126_15528.lax);
            lax_universes = (uu___126_15528.lax_universes);
            failhard = (uu___126_15528.failhard);
            nosynth = (uu___126_15528.nosynth);
            tc_term = (uu___126_15528.tc_term);
            type_of = (uu___126_15528.type_of);
            universe_of = (uu___126_15528.universe_of);
            check_type_of = (uu___126_15528.check_type_of);
            use_bv_sorts = (uu___126_15528.use_bv_sorts);
            qtbl_name_and_index = (uu___126_15528.qtbl_name_and_index);
            normalized_eff_names = (uu___126_15528.normalized_eff_names);
            proof_ns = (uu___126_15528.proof_ns);
            synth_hook = (uu___126_15528.synth_hook);
            splice = (uu___126_15528.splice);
            is_native_tactic = (uu___126_15528.is_native_tactic);
            identifier_info = (uu___126_15528.identifier_info);
            tc_hooks = (uu___126_15528.tc_hooks);
            dsenv = (uu___126_15528.dsenv);
            dep_graph = (uu___126_15528.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15558 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15558  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15716 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15717 = l1 u t wp e  in
                                l2 u t uu____15716 uu____15717))
                | uu____15718 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15790 = inst_tscheme_with lift_t [u]  in
            match uu____15790 with
            | (uu____15797,lift_t1) ->
                let uu____15799 =
                  let uu____15806 =
                    let uu____15807 =
                      let uu____15822 =
                        let uu____15831 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15838 =
                          let uu____15847 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____15847]  in
                        uu____15831 :: uu____15838  in
                      (lift_t1, uu____15822)  in
                    FStar_Syntax_Syntax.Tm_app uu____15807  in
                  FStar_Syntax_Syntax.mk uu____15806  in
                uu____15799 FStar_Pervasives_Native.None
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
            let uu____15949 = inst_tscheme_with lift_t [u]  in
            match uu____15949 with
            | (uu____15956,lift_t1) ->
                let uu____15958 =
                  let uu____15965 =
                    let uu____15966 =
                      let uu____15981 =
                        let uu____15990 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15997 =
                          let uu____16006 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16013 =
                            let uu____16022 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16022]  in
                          uu____16006 :: uu____16013  in
                        uu____15990 :: uu____15997  in
                      (lift_t1, uu____15981)  in
                    FStar_Syntax_Syntax.Tm_app uu____15966  in
                  FStar_Syntax_Syntax.mk uu____15965  in
                uu____15958 FStar_Pervasives_Native.None
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
              let uu____16112 =
                let uu____16113 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16113
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16112  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16117 =
              let uu____16118 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16118  in
            let uu____16119 =
              let uu____16120 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16146 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16146)
                 in
              FStar_Util.dflt "none" uu____16120  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16117
              uu____16119
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16172  ->
                    match uu____16172 with
                    | (e,uu____16180) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16203 =
            match uu____16203 with
            | (i,j) ->
                let uu____16214 = FStar_Ident.lid_equals i j  in
                if uu____16214
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
              let uu____16246 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16256 = FStar_Ident.lid_equals i k  in
                        if uu____16256
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16267 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16267
                                  then []
                                  else
                                    (let uu____16271 =
                                       let uu____16280 =
                                         find_edge order1 (i, k)  in
                                       let uu____16283 =
                                         find_edge order1 (k, j)  in
                                       (uu____16280, uu____16283)  in
                                     match uu____16271 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16298 =
                                           compose_edges e1 e2  in
                                         [uu____16298]
                                     | uu____16299 -> [])))))
                 in
              FStar_List.append order1 uu____16246  in
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
                   let uu____16329 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16331 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16331
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16329
                   then
                     let uu____16336 =
                       let uu____16341 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16341)
                        in
                     let uu____16342 = get_range env  in
                     FStar_Errors.raise_error uu____16336 uu____16342
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16419 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16419
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16468 =
                                              let uu____16477 =
                                                find_edge order2 (i, k)  in
                                              let uu____16480 =
                                                find_edge order2 (j, k)  in
                                              (uu____16477, uu____16480)  in
                                            match uu____16468 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16522,uu____16523)
                                                     ->
                                                     let uu____16530 =
                                                       let uu____16535 =
                                                         let uu____16536 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16536
                                                          in
                                                       let uu____16539 =
                                                         let uu____16540 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16540
                                                          in
                                                       (uu____16535,
                                                         uu____16539)
                                                        in
                                                     (match uu____16530 with
                                                      | (true ,true ) ->
                                                          let uu____16551 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16551
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
                                            | uu____16576 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___127_16649 = env.effects  in
              { decls = (uu___127_16649.decls); order = order2; joins }  in
            let uu___128_16650 = env  in
            {
              solver = (uu___128_16650.solver);
              range = (uu___128_16650.range);
              curmodule = (uu___128_16650.curmodule);
              gamma = (uu___128_16650.gamma);
              gamma_sig = (uu___128_16650.gamma_sig);
              gamma_cache = (uu___128_16650.gamma_cache);
              modules = (uu___128_16650.modules);
              expected_typ = (uu___128_16650.expected_typ);
              sigtab = (uu___128_16650.sigtab);
              is_pattern = (uu___128_16650.is_pattern);
              instantiate_imp = (uu___128_16650.instantiate_imp);
              effects;
              generalize = (uu___128_16650.generalize);
              letrecs = (uu___128_16650.letrecs);
              top_level = (uu___128_16650.top_level);
              check_uvars = (uu___128_16650.check_uvars);
              use_eq = (uu___128_16650.use_eq);
              is_iface = (uu___128_16650.is_iface);
              admit = (uu___128_16650.admit);
              lax = (uu___128_16650.lax);
              lax_universes = (uu___128_16650.lax_universes);
              failhard = (uu___128_16650.failhard);
              nosynth = (uu___128_16650.nosynth);
              tc_term = (uu___128_16650.tc_term);
              type_of = (uu___128_16650.type_of);
              universe_of = (uu___128_16650.universe_of);
              check_type_of = (uu___128_16650.check_type_of);
              use_bv_sorts = (uu___128_16650.use_bv_sorts);
              qtbl_name_and_index = (uu___128_16650.qtbl_name_and_index);
              normalized_eff_names = (uu___128_16650.normalized_eff_names);
              proof_ns = (uu___128_16650.proof_ns);
              synth_hook = (uu___128_16650.synth_hook);
              splice = (uu___128_16650.splice);
              is_native_tactic = (uu___128_16650.is_native_tactic);
              identifier_info = (uu___128_16650.identifier_info);
              tc_hooks = (uu___128_16650.tc_hooks);
              dsenv = (uu___128_16650.dsenv);
              dep_graph = (uu___128_16650.dep_graph)
            }))
      | uu____16651 -> env
  
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
        | uu____16679 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16691 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16691 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16708 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16708 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16727 =
                     let uu____16732 =
                       let uu____16733 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16738 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16745 =
                         let uu____16746 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16746  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16733 uu____16738 uu____16745
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16732)
                      in
                   FStar_Errors.raise_error uu____16727
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16751 =
                     let uu____16760 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16760 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16789  ->
                        fun uu____16790  ->
                          match (uu____16789, uu____16790) with
                          | ((x,uu____16812),(t,uu____16814)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16751
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____16833 =
                     let uu___129_16834 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___129_16834.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___129_16834.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___129_16834.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___129_16834.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____16833
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
          let uu____16864 = effect_decl_opt env effect_name  in
          match uu____16864 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____16897 =
                only_reifiable &&
                  (let uu____16899 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____16899)
                 in
              if uu____16897
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____16915 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____16934 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____16963 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____16963
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____16964 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____16964
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____16976 =
                       let uu____16979 = get_range env  in
                       let uu____16980 =
                         let uu____16987 =
                           let uu____16988 =
                             let uu____17003 =
                               let uu____17012 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17012; wp]  in
                             (repr, uu____17003)  in
                           FStar_Syntax_Syntax.Tm_app uu____16988  in
                         FStar_Syntax_Syntax.mk uu____16987  in
                       uu____16980 FStar_Pervasives_Native.None uu____16979
                        in
                     FStar_Pervasives_Native.Some uu____16976)
  
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
          let uu____17092 =
            let uu____17097 =
              let uu____17098 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17098
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17097)  in
          let uu____17099 = get_range env  in
          FStar_Errors.raise_error uu____17092 uu____17099  in
        let uu____17100 = effect_repr_aux true env c u_c  in
        match uu____17100 with
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
      | uu____17146 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17157 =
        let uu____17158 = FStar_Syntax_Subst.compress t  in
        uu____17158.FStar_Syntax_Syntax.n  in
      match uu____17157 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17161,c) ->
          is_reifiable_comp env c
      | uu____17179 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___130_17200 = env  in
        {
          solver = (uu___130_17200.solver);
          range = (uu___130_17200.range);
          curmodule = (uu___130_17200.curmodule);
          gamma = (uu___130_17200.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___130_17200.gamma_cache);
          modules = (uu___130_17200.modules);
          expected_typ = (uu___130_17200.expected_typ);
          sigtab = (uu___130_17200.sigtab);
          is_pattern = (uu___130_17200.is_pattern);
          instantiate_imp = (uu___130_17200.instantiate_imp);
          effects = (uu___130_17200.effects);
          generalize = (uu___130_17200.generalize);
          letrecs = (uu___130_17200.letrecs);
          top_level = (uu___130_17200.top_level);
          check_uvars = (uu___130_17200.check_uvars);
          use_eq = (uu___130_17200.use_eq);
          is_iface = (uu___130_17200.is_iface);
          admit = (uu___130_17200.admit);
          lax = (uu___130_17200.lax);
          lax_universes = (uu___130_17200.lax_universes);
          failhard = (uu___130_17200.failhard);
          nosynth = (uu___130_17200.nosynth);
          tc_term = (uu___130_17200.tc_term);
          type_of = (uu___130_17200.type_of);
          universe_of = (uu___130_17200.universe_of);
          check_type_of = (uu___130_17200.check_type_of);
          use_bv_sorts = (uu___130_17200.use_bv_sorts);
          qtbl_name_and_index = (uu___130_17200.qtbl_name_and_index);
          normalized_eff_names = (uu___130_17200.normalized_eff_names);
          proof_ns = (uu___130_17200.proof_ns);
          synth_hook = (uu___130_17200.synth_hook);
          splice = (uu___130_17200.splice);
          is_native_tactic = (uu___130_17200.is_native_tactic);
          identifier_info = (uu___130_17200.identifier_info);
          tc_hooks = (uu___130_17200.tc_hooks);
          dsenv = (uu___130_17200.dsenv);
          dep_graph = (uu___130_17200.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___131_17212 = env  in
      {
        solver = (uu___131_17212.solver);
        range = (uu___131_17212.range);
        curmodule = (uu___131_17212.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___131_17212.gamma_sig);
        gamma_cache = (uu___131_17212.gamma_cache);
        modules = (uu___131_17212.modules);
        expected_typ = (uu___131_17212.expected_typ);
        sigtab = (uu___131_17212.sigtab);
        is_pattern = (uu___131_17212.is_pattern);
        instantiate_imp = (uu___131_17212.instantiate_imp);
        effects = (uu___131_17212.effects);
        generalize = (uu___131_17212.generalize);
        letrecs = (uu___131_17212.letrecs);
        top_level = (uu___131_17212.top_level);
        check_uvars = (uu___131_17212.check_uvars);
        use_eq = (uu___131_17212.use_eq);
        is_iface = (uu___131_17212.is_iface);
        admit = (uu___131_17212.admit);
        lax = (uu___131_17212.lax);
        lax_universes = (uu___131_17212.lax_universes);
        failhard = (uu___131_17212.failhard);
        nosynth = (uu___131_17212.nosynth);
        tc_term = (uu___131_17212.tc_term);
        type_of = (uu___131_17212.type_of);
        universe_of = (uu___131_17212.universe_of);
        check_type_of = (uu___131_17212.check_type_of);
        use_bv_sorts = (uu___131_17212.use_bv_sorts);
        qtbl_name_and_index = (uu___131_17212.qtbl_name_and_index);
        normalized_eff_names = (uu___131_17212.normalized_eff_names);
        proof_ns = (uu___131_17212.proof_ns);
        synth_hook = (uu___131_17212.synth_hook);
        splice = (uu___131_17212.splice);
        is_native_tactic = (uu___131_17212.is_native_tactic);
        identifier_info = (uu___131_17212.identifier_info);
        tc_hooks = (uu___131_17212.tc_hooks);
        dsenv = (uu___131_17212.dsenv);
        dep_graph = (uu___131_17212.dep_graph)
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
            (let uu___132_17267 = env  in
             {
               solver = (uu___132_17267.solver);
               range = (uu___132_17267.range);
               curmodule = (uu___132_17267.curmodule);
               gamma = rest;
               gamma_sig = (uu___132_17267.gamma_sig);
               gamma_cache = (uu___132_17267.gamma_cache);
               modules = (uu___132_17267.modules);
               expected_typ = (uu___132_17267.expected_typ);
               sigtab = (uu___132_17267.sigtab);
               is_pattern = (uu___132_17267.is_pattern);
               instantiate_imp = (uu___132_17267.instantiate_imp);
               effects = (uu___132_17267.effects);
               generalize = (uu___132_17267.generalize);
               letrecs = (uu___132_17267.letrecs);
               top_level = (uu___132_17267.top_level);
               check_uvars = (uu___132_17267.check_uvars);
               use_eq = (uu___132_17267.use_eq);
               is_iface = (uu___132_17267.is_iface);
               admit = (uu___132_17267.admit);
               lax = (uu___132_17267.lax);
               lax_universes = (uu___132_17267.lax_universes);
               failhard = (uu___132_17267.failhard);
               nosynth = (uu___132_17267.nosynth);
               tc_term = (uu___132_17267.tc_term);
               type_of = (uu___132_17267.type_of);
               universe_of = (uu___132_17267.universe_of);
               check_type_of = (uu___132_17267.check_type_of);
               use_bv_sorts = (uu___132_17267.use_bv_sorts);
               qtbl_name_and_index = (uu___132_17267.qtbl_name_and_index);
               normalized_eff_names = (uu___132_17267.normalized_eff_names);
               proof_ns = (uu___132_17267.proof_ns);
               synth_hook = (uu___132_17267.synth_hook);
               splice = (uu___132_17267.splice);
               is_native_tactic = (uu___132_17267.is_native_tactic);
               identifier_info = (uu___132_17267.identifier_info);
               tc_hooks = (uu___132_17267.tc_hooks);
               dsenv = (uu___132_17267.dsenv);
               dep_graph = (uu___132_17267.dep_graph)
             }))
    | uu____17268 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17294  ->
             match uu____17294 with | (x,uu____17300) -> push_bv env1 x) env
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
            let uu___133_17330 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_17330.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_17330.FStar_Syntax_Syntax.index);
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
      (let uu___134_17370 = env  in
       {
         solver = (uu___134_17370.solver);
         range = (uu___134_17370.range);
         curmodule = (uu___134_17370.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___134_17370.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___134_17370.sigtab);
         is_pattern = (uu___134_17370.is_pattern);
         instantiate_imp = (uu___134_17370.instantiate_imp);
         effects = (uu___134_17370.effects);
         generalize = (uu___134_17370.generalize);
         letrecs = (uu___134_17370.letrecs);
         top_level = (uu___134_17370.top_level);
         check_uvars = (uu___134_17370.check_uvars);
         use_eq = (uu___134_17370.use_eq);
         is_iface = (uu___134_17370.is_iface);
         admit = (uu___134_17370.admit);
         lax = (uu___134_17370.lax);
         lax_universes = (uu___134_17370.lax_universes);
         failhard = (uu___134_17370.failhard);
         nosynth = (uu___134_17370.nosynth);
         tc_term = (uu___134_17370.tc_term);
         type_of = (uu___134_17370.type_of);
         universe_of = (uu___134_17370.universe_of);
         check_type_of = (uu___134_17370.check_type_of);
         use_bv_sorts = (uu___134_17370.use_bv_sorts);
         qtbl_name_and_index = (uu___134_17370.qtbl_name_and_index);
         normalized_eff_names = (uu___134_17370.normalized_eff_names);
         proof_ns = (uu___134_17370.proof_ns);
         synth_hook = (uu___134_17370.synth_hook);
         splice = (uu___134_17370.splice);
         is_native_tactic = (uu___134_17370.is_native_tactic);
         identifier_info = (uu___134_17370.identifier_info);
         tc_hooks = (uu___134_17370.tc_hooks);
         dsenv = (uu___134_17370.dsenv);
         dep_graph = (uu___134_17370.dep_graph)
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
        let uu____17412 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17412 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17440 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17440)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___135_17455 = env  in
      {
        solver = (uu___135_17455.solver);
        range = (uu___135_17455.range);
        curmodule = (uu___135_17455.curmodule);
        gamma = (uu___135_17455.gamma);
        gamma_sig = (uu___135_17455.gamma_sig);
        gamma_cache = (uu___135_17455.gamma_cache);
        modules = (uu___135_17455.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___135_17455.sigtab);
        is_pattern = (uu___135_17455.is_pattern);
        instantiate_imp = (uu___135_17455.instantiate_imp);
        effects = (uu___135_17455.effects);
        generalize = (uu___135_17455.generalize);
        letrecs = (uu___135_17455.letrecs);
        top_level = (uu___135_17455.top_level);
        check_uvars = (uu___135_17455.check_uvars);
        use_eq = false;
        is_iface = (uu___135_17455.is_iface);
        admit = (uu___135_17455.admit);
        lax = (uu___135_17455.lax);
        lax_universes = (uu___135_17455.lax_universes);
        failhard = (uu___135_17455.failhard);
        nosynth = (uu___135_17455.nosynth);
        tc_term = (uu___135_17455.tc_term);
        type_of = (uu___135_17455.type_of);
        universe_of = (uu___135_17455.universe_of);
        check_type_of = (uu___135_17455.check_type_of);
        use_bv_sorts = (uu___135_17455.use_bv_sorts);
        qtbl_name_and_index = (uu___135_17455.qtbl_name_and_index);
        normalized_eff_names = (uu___135_17455.normalized_eff_names);
        proof_ns = (uu___135_17455.proof_ns);
        synth_hook = (uu___135_17455.synth_hook);
        splice = (uu___135_17455.splice);
        is_native_tactic = (uu___135_17455.is_native_tactic);
        identifier_info = (uu___135_17455.identifier_info);
        tc_hooks = (uu___135_17455.tc_hooks);
        dsenv = (uu___135_17455.dsenv);
        dep_graph = (uu___135_17455.dep_graph)
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
    let uu____17483 = expected_typ env_  in
    ((let uu___136_17489 = env_  in
      {
        solver = (uu___136_17489.solver);
        range = (uu___136_17489.range);
        curmodule = (uu___136_17489.curmodule);
        gamma = (uu___136_17489.gamma);
        gamma_sig = (uu___136_17489.gamma_sig);
        gamma_cache = (uu___136_17489.gamma_cache);
        modules = (uu___136_17489.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___136_17489.sigtab);
        is_pattern = (uu___136_17489.is_pattern);
        instantiate_imp = (uu___136_17489.instantiate_imp);
        effects = (uu___136_17489.effects);
        generalize = (uu___136_17489.generalize);
        letrecs = (uu___136_17489.letrecs);
        top_level = (uu___136_17489.top_level);
        check_uvars = (uu___136_17489.check_uvars);
        use_eq = false;
        is_iface = (uu___136_17489.is_iface);
        admit = (uu___136_17489.admit);
        lax = (uu___136_17489.lax);
        lax_universes = (uu___136_17489.lax_universes);
        failhard = (uu___136_17489.failhard);
        nosynth = (uu___136_17489.nosynth);
        tc_term = (uu___136_17489.tc_term);
        type_of = (uu___136_17489.type_of);
        universe_of = (uu___136_17489.universe_of);
        check_type_of = (uu___136_17489.check_type_of);
        use_bv_sorts = (uu___136_17489.use_bv_sorts);
        qtbl_name_and_index = (uu___136_17489.qtbl_name_and_index);
        normalized_eff_names = (uu___136_17489.normalized_eff_names);
        proof_ns = (uu___136_17489.proof_ns);
        synth_hook = (uu___136_17489.synth_hook);
        splice = (uu___136_17489.splice);
        is_native_tactic = (uu___136_17489.is_native_tactic);
        identifier_info = (uu___136_17489.identifier_info);
        tc_hooks = (uu___136_17489.tc_hooks);
        dsenv = (uu___136_17489.dsenv);
        dep_graph = (uu___136_17489.dep_graph)
      }), uu____17483)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17499 =
      let uu____17502 = FStar_Ident.id_of_text ""  in [uu____17502]  in
    FStar_Ident.lid_of_ids uu____17499  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17508 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17508
        then
          let uu____17511 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17511 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___137_17538 = env  in
       {
         solver = (uu___137_17538.solver);
         range = (uu___137_17538.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___137_17538.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___137_17538.expected_typ);
         sigtab = (uu___137_17538.sigtab);
         is_pattern = (uu___137_17538.is_pattern);
         instantiate_imp = (uu___137_17538.instantiate_imp);
         effects = (uu___137_17538.effects);
         generalize = (uu___137_17538.generalize);
         letrecs = (uu___137_17538.letrecs);
         top_level = (uu___137_17538.top_level);
         check_uvars = (uu___137_17538.check_uvars);
         use_eq = (uu___137_17538.use_eq);
         is_iface = (uu___137_17538.is_iface);
         admit = (uu___137_17538.admit);
         lax = (uu___137_17538.lax);
         lax_universes = (uu___137_17538.lax_universes);
         failhard = (uu___137_17538.failhard);
         nosynth = (uu___137_17538.nosynth);
         tc_term = (uu___137_17538.tc_term);
         type_of = (uu___137_17538.type_of);
         universe_of = (uu___137_17538.universe_of);
         check_type_of = (uu___137_17538.check_type_of);
         use_bv_sorts = (uu___137_17538.use_bv_sorts);
         qtbl_name_and_index = (uu___137_17538.qtbl_name_and_index);
         normalized_eff_names = (uu___137_17538.normalized_eff_names);
         proof_ns = (uu___137_17538.proof_ns);
         synth_hook = (uu___137_17538.synth_hook);
         splice = (uu___137_17538.splice);
         is_native_tactic = (uu___137_17538.is_native_tactic);
         identifier_info = (uu___137_17538.identifier_info);
         tc_hooks = (uu___137_17538.tc_hooks);
         dsenv = (uu___137_17538.dsenv);
         dep_graph = (uu___137_17538.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17589)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17593,(uu____17594,t)))::tl1
          ->
          let uu____17615 =
            let uu____17618 = FStar_Syntax_Free.uvars t  in
            ext out uu____17618  in
          aux uu____17615 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17621;
            FStar_Syntax_Syntax.index = uu____17622;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17629 =
            let uu____17632 = FStar_Syntax_Free.uvars t  in
            ext out uu____17632  in
          aux uu____17629 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17689)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17693,(uu____17694,t)))::tl1
          ->
          let uu____17715 =
            let uu____17718 = FStar_Syntax_Free.univs t  in
            ext out uu____17718  in
          aux uu____17715 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17721;
            FStar_Syntax_Syntax.index = uu____17722;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17729 =
            let uu____17732 = FStar_Syntax_Free.univs t  in
            ext out uu____17732  in
          aux uu____17729 tl1
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
          let uu____17793 = FStar_Util.set_add uname out  in
          aux uu____17793 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17796,(uu____17797,t)))::tl1
          ->
          let uu____17818 =
            let uu____17821 = FStar_Syntax_Free.univnames t  in
            ext out uu____17821  in
          aux uu____17818 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17824;
            FStar_Syntax_Syntax.index = uu____17825;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17832 =
            let uu____17835 = FStar_Syntax_Free.univnames t  in
            ext out uu____17835  in
          aux uu____17832 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___111_17855  ->
            match uu___111_17855 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____17859 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____17872 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____17882 =
      let uu____17889 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____17889
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____17882 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____17927 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___112_17937  ->
              match uu___112_17937 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____17939 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____17939
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____17942) ->
                  let uu____17959 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____17959))
       in
    FStar_All.pipe_right uu____17927 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___113_17966  ->
    match uu___113_17966 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____17967 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____17987  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18029) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18048,uu____18049) -> false  in
      let uu____18058 =
        FStar_List.tryFind
          (fun uu____18076  ->
             match uu____18076 with | (p,uu____18084) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18058 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18095,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18117 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18117
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___138_18135 = e  in
        {
          solver = (uu___138_18135.solver);
          range = (uu___138_18135.range);
          curmodule = (uu___138_18135.curmodule);
          gamma = (uu___138_18135.gamma);
          gamma_sig = (uu___138_18135.gamma_sig);
          gamma_cache = (uu___138_18135.gamma_cache);
          modules = (uu___138_18135.modules);
          expected_typ = (uu___138_18135.expected_typ);
          sigtab = (uu___138_18135.sigtab);
          is_pattern = (uu___138_18135.is_pattern);
          instantiate_imp = (uu___138_18135.instantiate_imp);
          effects = (uu___138_18135.effects);
          generalize = (uu___138_18135.generalize);
          letrecs = (uu___138_18135.letrecs);
          top_level = (uu___138_18135.top_level);
          check_uvars = (uu___138_18135.check_uvars);
          use_eq = (uu___138_18135.use_eq);
          is_iface = (uu___138_18135.is_iface);
          admit = (uu___138_18135.admit);
          lax = (uu___138_18135.lax);
          lax_universes = (uu___138_18135.lax_universes);
          failhard = (uu___138_18135.failhard);
          nosynth = (uu___138_18135.nosynth);
          tc_term = (uu___138_18135.tc_term);
          type_of = (uu___138_18135.type_of);
          universe_of = (uu___138_18135.universe_of);
          check_type_of = (uu___138_18135.check_type_of);
          use_bv_sorts = (uu___138_18135.use_bv_sorts);
          qtbl_name_and_index = (uu___138_18135.qtbl_name_and_index);
          normalized_eff_names = (uu___138_18135.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___138_18135.synth_hook);
          splice = (uu___138_18135.splice);
          is_native_tactic = (uu___138_18135.is_native_tactic);
          identifier_info = (uu___138_18135.identifier_info);
          tc_hooks = (uu___138_18135.tc_hooks);
          dsenv = (uu___138_18135.dsenv);
          dep_graph = (uu___138_18135.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___139_18175 = e  in
      {
        solver = (uu___139_18175.solver);
        range = (uu___139_18175.range);
        curmodule = (uu___139_18175.curmodule);
        gamma = (uu___139_18175.gamma);
        gamma_sig = (uu___139_18175.gamma_sig);
        gamma_cache = (uu___139_18175.gamma_cache);
        modules = (uu___139_18175.modules);
        expected_typ = (uu___139_18175.expected_typ);
        sigtab = (uu___139_18175.sigtab);
        is_pattern = (uu___139_18175.is_pattern);
        instantiate_imp = (uu___139_18175.instantiate_imp);
        effects = (uu___139_18175.effects);
        generalize = (uu___139_18175.generalize);
        letrecs = (uu___139_18175.letrecs);
        top_level = (uu___139_18175.top_level);
        check_uvars = (uu___139_18175.check_uvars);
        use_eq = (uu___139_18175.use_eq);
        is_iface = (uu___139_18175.is_iface);
        admit = (uu___139_18175.admit);
        lax = (uu___139_18175.lax);
        lax_universes = (uu___139_18175.lax_universes);
        failhard = (uu___139_18175.failhard);
        nosynth = (uu___139_18175.nosynth);
        tc_term = (uu___139_18175.tc_term);
        type_of = (uu___139_18175.type_of);
        universe_of = (uu___139_18175.universe_of);
        check_type_of = (uu___139_18175.check_type_of);
        use_bv_sorts = (uu___139_18175.use_bv_sorts);
        qtbl_name_and_index = (uu___139_18175.qtbl_name_and_index);
        normalized_eff_names = (uu___139_18175.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___139_18175.synth_hook);
        splice = (uu___139_18175.splice);
        is_native_tactic = (uu___139_18175.is_native_tactic);
        identifier_info = (uu___139_18175.identifier_info);
        tc_hooks = (uu___139_18175.tc_hooks);
        dsenv = (uu___139_18175.dsenv);
        dep_graph = (uu___139_18175.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18190 = FStar_Syntax_Free.names t  in
      let uu____18193 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18190 uu____18193
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18214 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18214
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18222 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18222
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18241 =
      match uu____18241 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18257 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18257)
       in
    let uu____18259 =
      let uu____18262 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18262 FStar_List.rev  in
    FStar_All.pipe_right uu____18259 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18277  -> ());
    push = (fun uu____18279  -> ());
    pop = (fun uu____18281  -> ());
    snapshot =
      (fun uu____18283  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18292  -> fun uu____18293  -> ());
    encode_modul = (fun uu____18304  -> fun uu____18305  -> ());
    encode_sig = (fun uu____18308  -> fun uu____18309  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18315 =
             let uu____18322 = FStar_Options.peek ()  in (e, g, uu____18322)
              in
           [uu____18315]);
    solve = (fun uu____18338  -> fun uu____18339  -> fun uu____18340  -> ());
    finish = (fun uu____18346  -> ());
    refresh = (fun uu____18348  -> ())
  } 