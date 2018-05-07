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
      FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list
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
      FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list)
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
    FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list[@@deriving
                                                                  show]
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___100_8086  ->
              match uu___100_8086 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8089 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8089  in
                  let uu____8090 =
                    let uu____8091 = FStar_Syntax_Subst.compress y  in
                    uu____8091.FStar_Syntax_Syntax.n  in
                  (match uu____8090 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8095 =
                         let uu___114_8096 = y1  in
                         let uu____8097 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___114_8096.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___114_8096.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8097
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8095
                   | uu____8100 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___115_8112 = env  in
      let uu____8113 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___115_8112.solver);
        range = (uu___115_8112.range);
        curmodule = (uu___115_8112.curmodule);
        gamma = uu____8113;
        gamma_sig = (uu___115_8112.gamma_sig);
        gamma_cache = (uu___115_8112.gamma_cache);
        modules = (uu___115_8112.modules);
        expected_typ = (uu___115_8112.expected_typ);
        sigtab = (uu___115_8112.sigtab);
        is_pattern = (uu___115_8112.is_pattern);
        instantiate_imp = (uu___115_8112.instantiate_imp);
        effects = (uu___115_8112.effects);
        generalize = (uu___115_8112.generalize);
        letrecs = (uu___115_8112.letrecs);
        top_level = (uu___115_8112.top_level);
        check_uvars = (uu___115_8112.check_uvars);
        use_eq = (uu___115_8112.use_eq);
        is_iface = (uu___115_8112.is_iface);
        admit = (uu___115_8112.admit);
        lax = (uu___115_8112.lax);
        lax_universes = (uu___115_8112.lax_universes);
        failhard = (uu___115_8112.failhard);
        nosynth = (uu___115_8112.nosynth);
        tc_term = (uu___115_8112.tc_term);
        type_of = (uu___115_8112.type_of);
        universe_of = (uu___115_8112.universe_of);
        check_type_of = (uu___115_8112.check_type_of);
        use_bv_sorts = (uu___115_8112.use_bv_sorts);
        qtbl_name_and_index = (uu___115_8112.qtbl_name_and_index);
        normalized_eff_names = (uu___115_8112.normalized_eff_names);
        proof_ns = (uu___115_8112.proof_ns);
        synth_hook = (uu___115_8112.synth_hook);
        splice = (uu___115_8112.splice);
        is_native_tactic = (uu___115_8112.is_native_tactic);
        identifier_info = (uu___115_8112.identifier_info);
        tc_hooks = (uu___115_8112.tc_hooks);
        dsenv = (uu___115_8112.dsenv);
        dep_graph = (uu___115_8112.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8120  -> fun uu____8121  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___116_8141 = env  in
      {
        solver = (uu___116_8141.solver);
        range = (uu___116_8141.range);
        curmodule = (uu___116_8141.curmodule);
        gamma = (uu___116_8141.gamma);
        gamma_sig = (uu___116_8141.gamma_sig);
        gamma_cache = (uu___116_8141.gamma_cache);
        modules = (uu___116_8141.modules);
        expected_typ = (uu___116_8141.expected_typ);
        sigtab = (uu___116_8141.sigtab);
        is_pattern = (uu___116_8141.is_pattern);
        instantiate_imp = (uu___116_8141.instantiate_imp);
        effects = (uu___116_8141.effects);
        generalize = (uu___116_8141.generalize);
        letrecs = (uu___116_8141.letrecs);
        top_level = (uu___116_8141.top_level);
        check_uvars = (uu___116_8141.check_uvars);
        use_eq = (uu___116_8141.use_eq);
        is_iface = (uu___116_8141.is_iface);
        admit = (uu___116_8141.admit);
        lax = (uu___116_8141.lax);
        lax_universes = (uu___116_8141.lax_universes);
        failhard = (uu___116_8141.failhard);
        nosynth = (uu___116_8141.nosynth);
        tc_term = (uu___116_8141.tc_term);
        type_of = (uu___116_8141.type_of);
        universe_of = (uu___116_8141.universe_of);
        check_type_of = (uu___116_8141.check_type_of);
        use_bv_sorts = (uu___116_8141.use_bv_sorts);
        qtbl_name_and_index = (uu___116_8141.qtbl_name_and_index);
        normalized_eff_names = (uu___116_8141.normalized_eff_names);
        proof_ns = (uu___116_8141.proof_ns);
        synth_hook = (uu___116_8141.synth_hook);
        splice = (uu___116_8141.splice);
        is_native_tactic = (uu___116_8141.is_native_tactic);
        identifier_info = (uu___116_8141.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___116_8141.dsenv);
        dep_graph = (uu___116_8141.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___117_8152 = e  in
      {
        solver = (uu___117_8152.solver);
        range = (uu___117_8152.range);
        curmodule = (uu___117_8152.curmodule);
        gamma = (uu___117_8152.gamma);
        gamma_sig = (uu___117_8152.gamma_sig);
        gamma_cache = (uu___117_8152.gamma_cache);
        modules = (uu___117_8152.modules);
        expected_typ = (uu___117_8152.expected_typ);
        sigtab = (uu___117_8152.sigtab);
        is_pattern = (uu___117_8152.is_pattern);
        instantiate_imp = (uu___117_8152.instantiate_imp);
        effects = (uu___117_8152.effects);
        generalize = (uu___117_8152.generalize);
        letrecs = (uu___117_8152.letrecs);
        top_level = (uu___117_8152.top_level);
        check_uvars = (uu___117_8152.check_uvars);
        use_eq = (uu___117_8152.use_eq);
        is_iface = (uu___117_8152.is_iface);
        admit = (uu___117_8152.admit);
        lax = (uu___117_8152.lax);
        lax_universes = (uu___117_8152.lax_universes);
        failhard = (uu___117_8152.failhard);
        nosynth = (uu___117_8152.nosynth);
        tc_term = (uu___117_8152.tc_term);
        type_of = (uu___117_8152.type_of);
        universe_of = (uu___117_8152.universe_of);
        check_type_of = (uu___117_8152.check_type_of);
        use_bv_sorts = (uu___117_8152.use_bv_sorts);
        qtbl_name_and_index = (uu___117_8152.qtbl_name_and_index);
        normalized_eff_names = (uu___117_8152.normalized_eff_names);
        proof_ns = (uu___117_8152.proof_ns);
        synth_hook = (uu___117_8152.synth_hook);
        splice = (uu___117_8152.splice);
        is_native_tactic = (uu___117_8152.is_native_tactic);
        identifier_info = (uu___117_8152.identifier_info);
        tc_hooks = (uu___117_8152.tc_hooks);
        dsenv = (uu___117_8152.dsenv);
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
      | (NoDelta ,uu____8175) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8176,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8177,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8178 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8187 . unit -> 'Auu____8187 FStar_Util.smap =
  fun uu____8194  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8199 . unit -> 'Auu____8199 FStar_Util.smap =
  fun uu____8206  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8316 = new_gamma_cache ()  in
                let uu____8319 = new_sigtab ()  in
                let uu____8322 =
                  let uu____8335 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8335, FStar_Pervasives_Native.None)  in
                let uu____8350 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8353 = FStar_Options.using_facts_from ()  in
                let uu____8354 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8357 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____8316;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8319;
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
                  qtbl_name_and_index = uu____8322;
                  normalized_eff_names = uu____8350;
                  proof_ns = uu____8353;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8393  -> false);
                  identifier_info = uu____8354;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8357;
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
  fun uu____8484  ->
    let uu____8485 = FStar_ST.op_Bang query_indices  in
    match uu____8485 with
    | [] -> failwith "Empty query indices!"
    | uu____8539 ->
        let uu____8548 =
          let uu____8557 =
            let uu____8564 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8564  in
          let uu____8618 = FStar_ST.op_Bang query_indices  in uu____8557 ::
            uu____8618
           in
        FStar_ST.op_Colon_Equals query_indices uu____8548
  
let (pop_query_indices : unit -> unit) =
  fun uu____8715  ->
    let uu____8716 = FStar_ST.op_Bang query_indices  in
    match uu____8716 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____8839  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8869  ->
    match uu____8869 with
    | (l,n1) ->
        let uu____8876 = FStar_ST.op_Bang query_indices  in
        (match uu____8876 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____8995 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9014  ->
    let uu____9015 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9015
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9092 =
       let uu____9095 = FStar_ST.op_Bang stack  in env :: uu____9095  in
     FStar_ST.op_Colon_Equals stack uu____9092);
    (let uu___118_9152 = env  in
     let uu____9153 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9156 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9159 =
       let uu____9172 =
         let uu____9175 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9175  in
       let uu____9200 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9172, uu____9200)  in
     let uu____9241 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9244 =
       let uu____9247 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9247  in
     {
       solver = (uu___118_9152.solver);
       range = (uu___118_9152.range);
       curmodule = (uu___118_9152.curmodule);
       gamma = (uu___118_9152.gamma);
       gamma_sig = (uu___118_9152.gamma_sig);
       gamma_cache = uu____9153;
       modules = (uu___118_9152.modules);
       expected_typ = (uu___118_9152.expected_typ);
       sigtab = uu____9156;
       is_pattern = (uu___118_9152.is_pattern);
       instantiate_imp = (uu___118_9152.instantiate_imp);
       effects = (uu___118_9152.effects);
       generalize = (uu___118_9152.generalize);
       letrecs = (uu___118_9152.letrecs);
       top_level = (uu___118_9152.top_level);
       check_uvars = (uu___118_9152.check_uvars);
       use_eq = (uu___118_9152.use_eq);
       is_iface = (uu___118_9152.is_iface);
       admit = (uu___118_9152.admit);
       lax = (uu___118_9152.lax);
       lax_universes = (uu___118_9152.lax_universes);
       failhard = (uu___118_9152.failhard);
       nosynth = (uu___118_9152.nosynth);
       tc_term = (uu___118_9152.tc_term);
       type_of = (uu___118_9152.type_of);
       universe_of = (uu___118_9152.universe_of);
       check_type_of = (uu___118_9152.check_type_of);
       use_bv_sorts = (uu___118_9152.use_bv_sorts);
       qtbl_name_and_index = uu____9159;
       normalized_eff_names = uu____9241;
       proof_ns = (uu___118_9152.proof_ns);
       synth_hook = (uu___118_9152.synth_hook);
       splice = (uu___118_9152.splice);
       is_native_tactic = (uu___118_9152.is_native_tactic);
       identifier_info = uu____9244;
       tc_hooks = (uu___118_9152.tc_hooks);
       dsenv = (uu___118_9152.dsenv);
       dep_graph = (uu___118_9152.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9297  ->
    let uu____9298 = FStar_ST.op_Bang stack  in
    match uu____9298 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9360 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____9432  ->
           let uu____9433 = snapshot_stack env  in
           match uu____9433 with
           | (stack_depth,env1) ->
               let uu____9458 = snapshot_query_indices ()  in
               (match uu____9458 with
                | (query_indices_depth,()) ->
                    let uu____9482 = (env1.solver).snapshot msg  in
                    (match uu____9482 with
                     | (solver_depth,()) ->
                         let uu____9524 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9524 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___119_9570 = env1  in
                                 {
                                   solver = (uu___119_9570.solver);
                                   range = (uu___119_9570.range);
                                   curmodule = (uu___119_9570.curmodule);
                                   gamma = (uu___119_9570.gamma);
                                   gamma_sig = (uu___119_9570.gamma_sig);
                                   gamma_cache = (uu___119_9570.gamma_cache);
                                   modules = (uu___119_9570.modules);
                                   expected_typ =
                                     (uu___119_9570.expected_typ);
                                   sigtab = (uu___119_9570.sigtab);
                                   is_pattern = (uu___119_9570.is_pattern);
                                   instantiate_imp =
                                     (uu___119_9570.instantiate_imp);
                                   effects = (uu___119_9570.effects);
                                   generalize = (uu___119_9570.generalize);
                                   letrecs = (uu___119_9570.letrecs);
                                   top_level = (uu___119_9570.top_level);
                                   check_uvars = (uu___119_9570.check_uvars);
                                   use_eq = (uu___119_9570.use_eq);
                                   is_iface = (uu___119_9570.is_iface);
                                   admit = (uu___119_9570.admit);
                                   lax = (uu___119_9570.lax);
                                   lax_universes =
                                     (uu___119_9570.lax_universes);
                                   failhard = (uu___119_9570.failhard);
                                   nosynth = (uu___119_9570.nosynth);
                                   tc_term = (uu___119_9570.tc_term);
                                   type_of = (uu___119_9570.type_of);
                                   universe_of = (uu___119_9570.universe_of);
                                   check_type_of =
                                     (uu___119_9570.check_type_of);
                                   use_bv_sorts =
                                     (uu___119_9570.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___119_9570.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___119_9570.normalized_eff_names);
                                   proof_ns = (uu___119_9570.proof_ns);
                                   synth_hook = (uu___119_9570.synth_hook);
                                   splice = (uu___119_9570.splice);
                                   is_native_tactic =
                                     (uu___119_9570.is_native_tactic);
                                   identifier_info =
                                     (uu___119_9570.identifier_info);
                                   tc_hooks = (uu___119_9570.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___119_9570.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9601  ->
             let uu____9602 =
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
             match uu____9602 with
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
                             ((let uu____9680 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9680
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9691 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9691
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9718,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9750 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9776  ->
                  match uu____9776 with
                  | (m,uu____9782) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9750 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___120_9790 = env  in
               {
                 solver = (uu___120_9790.solver);
                 range = (uu___120_9790.range);
                 curmodule = (uu___120_9790.curmodule);
                 gamma = (uu___120_9790.gamma);
                 gamma_sig = (uu___120_9790.gamma_sig);
                 gamma_cache = (uu___120_9790.gamma_cache);
                 modules = (uu___120_9790.modules);
                 expected_typ = (uu___120_9790.expected_typ);
                 sigtab = (uu___120_9790.sigtab);
                 is_pattern = (uu___120_9790.is_pattern);
                 instantiate_imp = (uu___120_9790.instantiate_imp);
                 effects = (uu___120_9790.effects);
                 generalize = (uu___120_9790.generalize);
                 letrecs = (uu___120_9790.letrecs);
                 top_level = (uu___120_9790.top_level);
                 check_uvars = (uu___120_9790.check_uvars);
                 use_eq = (uu___120_9790.use_eq);
                 is_iface = (uu___120_9790.is_iface);
                 admit = (uu___120_9790.admit);
                 lax = (uu___120_9790.lax);
                 lax_universes = (uu___120_9790.lax_universes);
                 failhard = (uu___120_9790.failhard);
                 nosynth = (uu___120_9790.nosynth);
                 tc_term = (uu___120_9790.tc_term);
                 type_of = (uu___120_9790.type_of);
                 universe_of = (uu___120_9790.universe_of);
                 check_type_of = (uu___120_9790.check_type_of);
                 use_bv_sorts = (uu___120_9790.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___120_9790.normalized_eff_names);
                 proof_ns = (uu___120_9790.proof_ns);
                 synth_hook = (uu___120_9790.synth_hook);
                 splice = (uu___120_9790.splice);
                 is_native_tactic = (uu___120_9790.is_native_tactic);
                 identifier_info = (uu___120_9790.identifier_info);
                 tc_hooks = (uu___120_9790.tc_hooks);
                 dsenv = (uu___120_9790.dsenv);
                 dep_graph = (uu___120_9790.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9803,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___121_9812 = env  in
               {
                 solver = (uu___121_9812.solver);
                 range = (uu___121_9812.range);
                 curmodule = (uu___121_9812.curmodule);
                 gamma = (uu___121_9812.gamma);
                 gamma_sig = (uu___121_9812.gamma_sig);
                 gamma_cache = (uu___121_9812.gamma_cache);
                 modules = (uu___121_9812.modules);
                 expected_typ = (uu___121_9812.expected_typ);
                 sigtab = (uu___121_9812.sigtab);
                 is_pattern = (uu___121_9812.is_pattern);
                 instantiate_imp = (uu___121_9812.instantiate_imp);
                 effects = (uu___121_9812.effects);
                 generalize = (uu___121_9812.generalize);
                 letrecs = (uu___121_9812.letrecs);
                 top_level = (uu___121_9812.top_level);
                 check_uvars = (uu___121_9812.check_uvars);
                 use_eq = (uu___121_9812.use_eq);
                 is_iface = (uu___121_9812.is_iface);
                 admit = (uu___121_9812.admit);
                 lax = (uu___121_9812.lax);
                 lax_universes = (uu___121_9812.lax_universes);
                 failhard = (uu___121_9812.failhard);
                 nosynth = (uu___121_9812.nosynth);
                 tc_term = (uu___121_9812.tc_term);
                 type_of = (uu___121_9812.type_of);
                 universe_of = (uu___121_9812.universe_of);
                 check_type_of = (uu___121_9812.check_type_of);
                 use_bv_sorts = (uu___121_9812.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___121_9812.normalized_eff_names);
                 proof_ns = (uu___121_9812.proof_ns);
                 synth_hook = (uu___121_9812.synth_hook);
                 splice = (uu___121_9812.splice);
                 is_native_tactic = (uu___121_9812.is_native_tactic);
                 identifier_info = (uu___121_9812.identifier_info);
                 tc_hooks = (uu___121_9812.tc_hooks);
                 dsenv = (uu___121_9812.dsenv);
                 dep_graph = (uu___121_9812.dep_graph)
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
        (let uu___122_9846 = e  in
         {
           solver = (uu___122_9846.solver);
           range = r;
           curmodule = (uu___122_9846.curmodule);
           gamma = (uu___122_9846.gamma);
           gamma_sig = (uu___122_9846.gamma_sig);
           gamma_cache = (uu___122_9846.gamma_cache);
           modules = (uu___122_9846.modules);
           expected_typ = (uu___122_9846.expected_typ);
           sigtab = (uu___122_9846.sigtab);
           is_pattern = (uu___122_9846.is_pattern);
           instantiate_imp = (uu___122_9846.instantiate_imp);
           effects = (uu___122_9846.effects);
           generalize = (uu___122_9846.generalize);
           letrecs = (uu___122_9846.letrecs);
           top_level = (uu___122_9846.top_level);
           check_uvars = (uu___122_9846.check_uvars);
           use_eq = (uu___122_9846.use_eq);
           is_iface = (uu___122_9846.is_iface);
           admit = (uu___122_9846.admit);
           lax = (uu___122_9846.lax);
           lax_universes = (uu___122_9846.lax_universes);
           failhard = (uu___122_9846.failhard);
           nosynth = (uu___122_9846.nosynth);
           tc_term = (uu___122_9846.tc_term);
           type_of = (uu___122_9846.type_of);
           universe_of = (uu___122_9846.universe_of);
           check_type_of = (uu___122_9846.check_type_of);
           use_bv_sorts = (uu___122_9846.use_bv_sorts);
           qtbl_name_and_index = (uu___122_9846.qtbl_name_and_index);
           normalized_eff_names = (uu___122_9846.normalized_eff_names);
           proof_ns = (uu___122_9846.proof_ns);
           synth_hook = (uu___122_9846.synth_hook);
           splice = (uu___122_9846.splice);
           is_native_tactic = (uu___122_9846.is_native_tactic);
           identifier_info = (uu___122_9846.identifier_info);
           tc_hooks = (uu___122_9846.tc_hooks);
           dsenv = (uu___122_9846.dsenv);
           dep_graph = (uu___122_9846.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____9862 =
        let uu____9863 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____9863 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9862
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____9925 =
          let uu____9926 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____9926 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9925
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____9988 =
          let uu____9989 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____9989 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9988
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10051 =
        let uu____10052 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10052 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10051
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___123_10121 = env  in
      {
        solver = (uu___123_10121.solver);
        range = (uu___123_10121.range);
        curmodule = lid;
        gamma = (uu___123_10121.gamma);
        gamma_sig = (uu___123_10121.gamma_sig);
        gamma_cache = (uu___123_10121.gamma_cache);
        modules = (uu___123_10121.modules);
        expected_typ = (uu___123_10121.expected_typ);
        sigtab = (uu___123_10121.sigtab);
        is_pattern = (uu___123_10121.is_pattern);
        instantiate_imp = (uu___123_10121.instantiate_imp);
        effects = (uu___123_10121.effects);
        generalize = (uu___123_10121.generalize);
        letrecs = (uu___123_10121.letrecs);
        top_level = (uu___123_10121.top_level);
        check_uvars = (uu___123_10121.check_uvars);
        use_eq = (uu___123_10121.use_eq);
        is_iface = (uu___123_10121.is_iface);
        admit = (uu___123_10121.admit);
        lax = (uu___123_10121.lax);
        lax_universes = (uu___123_10121.lax_universes);
        failhard = (uu___123_10121.failhard);
        nosynth = (uu___123_10121.nosynth);
        tc_term = (uu___123_10121.tc_term);
        type_of = (uu___123_10121.type_of);
        universe_of = (uu___123_10121.universe_of);
        check_type_of = (uu___123_10121.check_type_of);
        use_bv_sorts = (uu___123_10121.use_bv_sorts);
        qtbl_name_and_index = (uu___123_10121.qtbl_name_and_index);
        normalized_eff_names = (uu___123_10121.normalized_eff_names);
        proof_ns = (uu___123_10121.proof_ns);
        synth_hook = (uu___123_10121.synth_hook);
        splice = (uu___123_10121.splice);
        is_native_tactic = (uu___123_10121.is_native_tactic);
        identifier_info = (uu___123_10121.identifier_info);
        tc_hooks = (uu___123_10121.tc_hooks);
        dsenv = (uu___123_10121.dsenv);
        dep_graph = (uu___123_10121.dep_graph)
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
      let uu____10148 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10148
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10158 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10158)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10168 =
      let uu____10169 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10169  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10168)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10174  ->
    let uu____10175 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10175
  
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
      | ((formals,t),uu____10231) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10265 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10265)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___101_10281  ->
    match uu___101_10281 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10307  -> new_u_univ ()))
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
      let uu____10326 = inst_tscheme t  in
      match uu____10326 with
      | (us,t1) ->
          let uu____10337 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10337)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10357  ->
          match uu____10357 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10376 =
                         let uu____10377 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10378 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10379 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10380 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10377 uu____10378 uu____10379 uu____10380
                          in
                       failwith uu____10376)
                    else ();
                    (let uu____10382 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10382))
               | uu____10391 ->
                   let uu____10392 =
                     let uu____10393 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10393
                      in
                   failwith uu____10392)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10399 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10405 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10411 -> false
  
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
             | ([],uu____10453) -> Maybe
             | (uu____10460,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10479 -> No  in
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
          let uu____10570 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10570 with
          | FStar_Pervasives_Native.None  ->
              let uu____10593 =
                FStar_Util.find_map env.gamma
                  (fun uu___102_10637  ->
                     match uu___102_10637 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____10676 = FStar_Ident.lid_equals lid l  in
                         if uu____10676
                         then
                           let uu____10697 =
                             let uu____10716 =
                               let uu____10731 = inst_tscheme t  in
                               FStar_Util.Inl uu____10731  in
                             let uu____10746 = FStar_Ident.range_of_lid l  in
                             (uu____10716, uu____10746)  in
                           FStar_Pervasives_Native.Some uu____10697
                         else FStar_Pervasives_Native.None
                     | uu____10798 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____10593
                (fun uu____10836  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___103_10845  ->
                        match uu___103_10845 with
                        | (uu____10848,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____10850);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____10851;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____10852;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____10853;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____10854;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____10874 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____10874
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
                                  uu____10922 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____10929 -> cache t  in
                            let uu____10930 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____10930 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____10936 =
                                   let uu____10937 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____10937)
                                    in
                                 maybe_cache uu____10936)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11005 = find_in_sigtab env lid  in
         match uu____11005 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11092) ->
          add_sigelts env ses
      | uu____11101 ->
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
            | uu____11115 -> ()))

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
        (fun uu___104_11146  ->
           match uu___104_11146 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11164 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11225,lb::[]),uu____11227) ->
            let uu____11234 =
              let uu____11243 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11252 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11243, uu____11252)  in
            FStar_Pervasives_Native.Some uu____11234
        | FStar_Syntax_Syntax.Sig_let ((uu____11265,lbs),uu____11267) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11297 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11309 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11309
                     then
                       let uu____11320 =
                         let uu____11329 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11338 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11329, uu____11338)  in
                       FStar_Pervasives_Native.Some uu____11320
                     else FStar_Pervasives_Native.None)
        | uu____11360 -> FStar_Pervasives_Native.None
  
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
          let uu____11419 =
            let uu____11428 =
              let uu____11433 =
                let uu____11434 =
                  let uu____11437 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11437
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11434)  in
              inst_tscheme1 uu____11433  in
            (uu____11428, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11419
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11459,uu____11460) ->
          let uu____11465 =
            let uu____11474 =
              let uu____11479 =
                let uu____11480 =
                  let uu____11483 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11483  in
                (us, uu____11480)  in
              inst_tscheme1 uu____11479  in
            (uu____11474, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11465
      | uu____11502 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11590 =
          match uu____11590 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11686,uvs,t,uu____11689,uu____11690,uu____11691);
                      FStar_Syntax_Syntax.sigrng = uu____11692;
                      FStar_Syntax_Syntax.sigquals = uu____11693;
                      FStar_Syntax_Syntax.sigmeta = uu____11694;
                      FStar_Syntax_Syntax.sigattrs = uu____11695;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11716 =
                     let uu____11725 = inst_tscheme1 (uvs, t)  in
                     (uu____11725, rng)  in
                   FStar_Pervasives_Native.Some uu____11716
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11749;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11751;
                      FStar_Syntax_Syntax.sigattrs = uu____11752;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11769 =
                     let uu____11770 = in_cur_mod env l  in uu____11770 = Yes
                      in
                   if uu____11769
                   then
                     let uu____11781 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____11781
                      then
                        let uu____11794 =
                          let uu____11803 = inst_tscheme1 (uvs, t)  in
                          (uu____11803, rng)  in
                        FStar_Pervasives_Native.Some uu____11794
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____11834 =
                        let uu____11843 = inst_tscheme1 (uvs, t)  in
                        (uu____11843, rng)  in
                      FStar_Pervasives_Native.Some uu____11834)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11868,uu____11869);
                      FStar_Syntax_Syntax.sigrng = uu____11870;
                      FStar_Syntax_Syntax.sigquals = uu____11871;
                      FStar_Syntax_Syntax.sigmeta = uu____11872;
                      FStar_Syntax_Syntax.sigattrs = uu____11873;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____11912 =
                          let uu____11921 = inst_tscheme1 (uvs, k)  in
                          (uu____11921, rng)  in
                        FStar_Pervasives_Native.Some uu____11912
                    | uu____11942 ->
                        let uu____11943 =
                          let uu____11952 =
                            let uu____11957 =
                              let uu____11958 =
                                let uu____11961 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11961
                                 in
                              (uvs, uu____11958)  in
                            inst_tscheme1 uu____11957  in
                          (uu____11952, rng)  in
                        FStar_Pervasives_Native.Some uu____11943)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11984,uu____11985);
                      FStar_Syntax_Syntax.sigrng = uu____11986;
                      FStar_Syntax_Syntax.sigquals = uu____11987;
                      FStar_Syntax_Syntax.sigmeta = uu____11988;
                      FStar_Syntax_Syntax.sigattrs = uu____11989;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12029 =
                          let uu____12038 = inst_tscheme_with (uvs, k) us  in
                          (uu____12038, rng)  in
                        FStar_Pervasives_Native.Some uu____12029
                    | uu____12059 ->
                        let uu____12060 =
                          let uu____12069 =
                            let uu____12074 =
                              let uu____12075 =
                                let uu____12078 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12078
                                 in
                              (uvs, uu____12075)  in
                            inst_tscheme_with uu____12074 us  in
                          (uu____12069, rng)  in
                        FStar_Pervasives_Native.Some uu____12060)
               | FStar_Util.Inr se ->
                   let uu____12114 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12135;
                          FStar_Syntax_Syntax.sigrng = uu____12136;
                          FStar_Syntax_Syntax.sigquals = uu____12137;
                          FStar_Syntax_Syntax.sigmeta = uu____12138;
                          FStar_Syntax_Syntax.sigattrs = uu____12139;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12154 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12114
                     (FStar_Util.map_option
                        (fun uu____12202  ->
                           match uu____12202 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12233 =
          let uu____12244 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12244 mapper  in
        match uu____12233 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12318 =
              let uu____12329 =
                let uu____12336 =
                  let uu___124_12339 = t  in
                  let uu____12340 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___124_12339.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12340;
                    FStar_Syntax_Syntax.vars =
                      (uu___124_12339.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12336)  in
              (uu____12329, r)  in
            FStar_Pervasives_Native.Some uu____12318
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12387 = lookup_qname env l  in
      match uu____12387 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12406 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12458 = try_lookup_bv env bv  in
      match uu____12458 with
      | FStar_Pervasives_Native.None  ->
          let uu____12473 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12473 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12488 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12489 =
            let uu____12490 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12490  in
          (uu____12488, uu____12489)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12511 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12511 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12577 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12577  in
          let uu____12578 =
            let uu____12587 =
              let uu____12592 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12592)  in
            (uu____12587, r1)  in
          FStar_Pervasives_Native.Some uu____12578
  
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
        let uu____12626 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12626 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12659,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12684 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12684  in
            let uu____12685 =
              let uu____12690 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12690, r1)  in
            FStar_Pervasives_Native.Some uu____12685
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12713 = try_lookup_lid env l  in
      match uu____12713 with
      | FStar_Pervasives_Native.None  ->
          let uu____12740 = name_not_found l  in
          let uu____12745 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12740 uu____12745
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___105_12785  ->
              match uu___105_12785 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12787 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12806 = lookup_qname env lid  in
      match uu____12806 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12815,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12818;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12820;
              FStar_Syntax_Syntax.sigattrs = uu____12821;_},FStar_Pervasives_Native.None
            ),uu____12822)
          ->
          let uu____12871 =
            let uu____12878 =
              let uu____12879 =
                let uu____12882 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____12882 t  in
              (uvs, uu____12879)  in
            (uu____12878, q)  in
          FStar_Pervasives_Native.Some uu____12871
      | uu____12895 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12916 = lookup_qname env lid  in
      match uu____12916 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12921,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12924;
              FStar_Syntax_Syntax.sigquals = uu____12925;
              FStar_Syntax_Syntax.sigmeta = uu____12926;
              FStar_Syntax_Syntax.sigattrs = uu____12927;_},FStar_Pervasives_Native.None
            ),uu____12928)
          ->
          let uu____12977 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12977 (uvs, t)
      | uu____12982 ->
          let uu____12983 = name_not_found lid  in
          let uu____12988 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12983 uu____12988
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13007 = lookup_qname env lid  in
      match uu____13007 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13012,uvs,t,uu____13015,uu____13016,uu____13017);
              FStar_Syntax_Syntax.sigrng = uu____13018;
              FStar_Syntax_Syntax.sigquals = uu____13019;
              FStar_Syntax_Syntax.sigmeta = uu____13020;
              FStar_Syntax_Syntax.sigattrs = uu____13021;_},FStar_Pervasives_Native.None
            ),uu____13022)
          ->
          let uu____13075 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13075 (uvs, t)
      | uu____13080 ->
          let uu____13081 = name_not_found lid  in
          let uu____13086 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13081 uu____13086
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13107 = lookup_qname env lid  in
      match uu____13107 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13114,uu____13115,uu____13116,uu____13117,uu____13118,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13120;
              FStar_Syntax_Syntax.sigquals = uu____13121;
              FStar_Syntax_Syntax.sigmeta = uu____13122;
              FStar_Syntax_Syntax.sigattrs = uu____13123;_},uu____13124),uu____13125)
          -> (true, dcs)
      | uu____13186 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13199 = lookup_qname env lid  in
      match uu____13199 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13200,uu____13201,uu____13202,l,uu____13204,uu____13205);
              FStar_Syntax_Syntax.sigrng = uu____13206;
              FStar_Syntax_Syntax.sigquals = uu____13207;
              FStar_Syntax_Syntax.sigmeta = uu____13208;
              FStar_Syntax_Syntax.sigattrs = uu____13209;_},uu____13210),uu____13211)
          -> l
      | uu____13266 ->
          let uu____13267 =
            let uu____13268 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13268  in
          failwith uu____13267
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13317)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13368,lbs),uu____13370)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13392 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13392
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13424 -> FStar_Pervasives_Native.None)
        | uu____13429 -> FStar_Pervasives_Native.None
  
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
        let uu____13459 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13459
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13484),uu____13485) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13534 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13555 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13555
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13574 = lookup_qname env ftv  in
      match uu____13574 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13578) ->
          let uu____13623 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13623 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13644,t),r) ->
               let uu____13659 =
                 let uu____13660 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13660 t  in
               FStar_Pervasives_Native.Some uu____13659)
      | uu____13661 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13672 = try_lookup_effect_lid env ftv  in
      match uu____13672 with
      | FStar_Pervasives_Native.None  ->
          let uu____13675 = name_not_found ftv  in
          let uu____13680 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13675 uu____13680
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
        let uu____13703 = lookup_qname env lid0  in
        match uu____13703 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13714);
                FStar_Syntax_Syntax.sigrng = uu____13715;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13717;
                FStar_Syntax_Syntax.sigattrs = uu____13718;_},FStar_Pervasives_Native.None
              ),uu____13719)
            ->
            let lid1 =
              let uu____13773 =
                let uu____13774 = FStar_Ident.range_of_lid lid  in
                let uu____13775 =
                  let uu____13776 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____13776  in
                FStar_Range.set_use_range uu____13774 uu____13775  in
              FStar_Ident.set_lid_range lid uu____13773  in
            let uu____13777 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___106_13781  ->
                      match uu___106_13781 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13782 -> false))
               in
            if uu____13777
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13796 =
                      let uu____13797 =
                        let uu____13798 = get_range env  in
                        FStar_Range.string_of_range uu____13798  in
                      let uu____13799 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____13800 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13797 uu____13799 uu____13800
                       in
                    failwith uu____13796)
                  in
               match (binders, univs1) with
               | ([],uu____13815) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____13836,uu____13837::uu____13838::uu____13839) ->
                   let uu____13856 =
                     let uu____13857 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____13858 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____13857 uu____13858
                      in
                   failwith uu____13856
               | uu____13865 ->
                   let uu____13878 =
                     let uu____13883 =
                       let uu____13884 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____13884)  in
                     inst_tscheme_with uu____13883 insts  in
                   (match uu____13878 with
                    | (uu____13897,t) ->
                        let t1 =
                          let uu____13900 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____13900 t  in
                        let uu____13901 =
                          let uu____13902 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13902.FStar_Syntax_Syntax.n  in
                        (match uu____13901 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____13933 -> failwith "Impossible")))
        | uu____13940 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____13963 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____13963 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____13976,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____13983 = find1 l2  in
            (match uu____13983 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____13990 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____13990 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____13994 = find1 l  in
            (match uu____13994 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____13999 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____13999
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14013 = lookup_qname env l1  in
      match uu____14013 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14016;
              FStar_Syntax_Syntax.sigrng = uu____14017;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14019;
              FStar_Syntax_Syntax.sigattrs = uu____14020;_},uu____14021),uu____14022)
          -> q
      | uu____14073 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14094 =
          let uu____14095 =
            let uu____14096 = FStar_Util.string_of_int i  in
            let uu____14097 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14096 uu____14097
             in
          failwith uu____14095  in
        let uu____14098 = lookup_datacon env lid  in
        match uu____14098 with
        | (uu____14103,t) ->
            let uu____14105 =
              let uu____14106 = FStar_Syntax_Subst.compress t  in
              uu____14106.FStar_Syntax_Syntax.n  in
            (match uu____14105 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14110) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14141 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14141
                      FStar_Pervasives_Native.fst)
             | uu____14150 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14161 = lookup_qname env l  in
      match uu____14161 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14162,uu____14163,uu____14164);
              FStar_Syntax_Syntax.sigrng = uu____14165;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14167;
              FStar_Syntax_Syntax.sigattrs = uu____14168;_},uu____14169),uu____14170)
          ->
          FStar_Util.for_some
            (fun uu___107_14223  ->
               match uu___107_14223 with
               | FStar_Syntax_Syntax.Projector uu____14224 -> true
               | uu____14229 -> false) quals
      | uu____14230 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14241 = lookup_qname env lid  in
      match uu____14241 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14242,uu____14243,uu____14244,uu____14245,uu____14246,uu____14247);
              FStar_Syntax_Syntax.sigrng = uu____14248;
              FStar_Syntax_Syntax.sigquals = uu____14249;
              FStar_Syntax_Syntax.sigmeta = uu____14250;
              FStar_Syntax_Syntax.sigattrs = uu____14251;_},uu____14252),uu____14253)
          -> true
      | uu____14308 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14319 = lookup_qname env lid  in
      match uu____14319 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14320,uu____14321,uu____14322,uu____14323,uu____14324,uu____14325);
              FStar_Syntax_Syntax.sigrng = uu____14326;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14328;
              FStar_Syntax_Syntax.sigattrs = uu____14329;_},uu____14330),uu____14331)
          ->
          FStar_Util.for_some
            (fun uu___108_14392  ->
               match uu___108_14392 with
               | FStar_Syntax_Syntax.RecordType uu____14393 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14402 -> true
               | uu____14411 -> false) quals
      | uu____14412 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14418,uu____14419);
            FStar_Syntax_Syntax.sigrng = uu____14420;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14422;
            FStar_Syntax_Syntax.sigattrs = uu____14423;_},uu____14424),uu____14425)
        ->
        FStar_Util.for_some
          (fun uu___109_14482  ->
             match uu___109_14482 with
             | FStar_Syntax_Syntax.Action uu____14483 -> true
             | uu____14484 -> false) quals
    | uu____14485 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14496 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14496
  
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
      let uu____14510 =
        let uu____14511 = FStar_Syntax_Util.un_uinst head1  in
        uu____14511.FStar_Syntax_Syntax.n  in
      match uu____14510 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14515 ->
               true
           | uu____14516 -> false)
      | uu____14517 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14528 = lookup_qname env l  in
      match uu____14528 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14530),uu____14531) ->
          FStar_Util.for_some
            (fun uu___110_14579  ->
               match uu___110_14579 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14580 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14581 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14652 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14668) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14685 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14692 ->
                 FStar_Pervasives_Native.Some true
             | uu____14709 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14710 =
        let uu____14713 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14713 mapper  in
      match uu____14710 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14763 = lookup_qname env lid  in
      match uu____14763 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14764,uu____14765,tps,uu____14767,uu____14768,uu____14769);
              FStar_Syntax_Syntax.sigrng = uu____14770;
              FStar_Syntax_Syntax.sigquals = uu____14771;
              FStar_Syntax_Syntax.sigmeta = uu____14772;
              FStar_Syntax_Syntax.sigattrs = uu____14773;_},uu____14774),uu____14775)
          -> FStar_List.length tps
      | uu____14838 ->
          let uu____14839 = name_not_found lid  in
          let uu____14844 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14839 uu____14844
  
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
           (fun uu____14888  ->
              match uu____14888 with
              | (d,uu____14896) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____14911 = effect_decl_opt env l  in
      match uu____14911 with
      | FStar_Pervasives_Native.None  ->
          let uu____14926 = name_not_found l  in
          let uu____14931 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14926 uu____14931
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____14953  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____14972  ->
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
        let uu____15003 = FStar_Ident.lid_equals l1 l2  in
        if uu____15003
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15011 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15011
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15019 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15072  ->
                        match uu____15072 with
                        | (m1,m2,uu____15085,uu____15086,uu____15087) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15019 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15104 =
                    let uu____15109 =
                      let uu____15110 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15111 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15110
                        uu____15111
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15109)
                     in
                  FStar_Errors.raise_error uu____15104 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15118,uu____15119,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15152 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15152
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
  'Auu____15168 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15168)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15197 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15223  ->
                match uu____15223 with
                | (d,uu____15229) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15197 with
      | FStar_Pervasives_Native.None  ->
          let uu____15240 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15240
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15253 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15253 with
           | (uu____15268,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15284)::(wp,uu____15286)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15322 -> failwith "Impossible"))
  
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
          let uu____15375 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15375
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15377 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15377
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
                  let uu____15385 = get_range env  in
                  let uu____15386 =
                    let uu____15393 =
                      let uu____15394 =
                        let uu____15409 =
                          let uu____15418 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15418]  in
                        (null_wp, uu____15409)  in
                      FStar_Syntax_Syntax.Tm_app uu____15394  in
                    FStar_Syntax_Syntax.mk uu____15393  in
                  uu____15386 FStar_Pervasives_Native.None uu____15385  in
                let uu____15450 =
                  let uu____15451 =
                    let uu____15460 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15460]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15451;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15450))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___125_15491 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___125_15491.order);
              joins = (uu___125_15491.joins)
            }  in
          let uu___126_15500 = env  in
          {
            solver = (uu___126_15500.solver);
            range = (uu___126_15500.range);
            curmodule = (uu___126_15500.curmodule);
            gamma = (uu___126_15500.gamma);
            gamma_sig = (uu___126_15500.gamma_sig);
            gamma_cache = (uu___126_15500.gamma_cache);
            modules = (uu___126_15500.modules);
            expected_typ = (uu___126_15500.expected_typ);
            sigtab = (uu___126_15500.sigtab);
            is_pattern = (uu___126_15500.is_pattern);
            instantiate_imp = (uu___126_15500.instantiate_imp);
            effects;
            generalize = (uu___126_15500.generalize);
            letrecs = (uu___126_15500.letrecs);
            top_level = (uu___126_15500.top_level);
            check_uvars = (uu___126_15500.check_uvars);
            use_eq = (uu___126_15500.use_eq);
            is_iface = (uu___126_15500.is_iface);
            admit = (uu___126_15500.admit);
            lax = (uu___126_15500.lax);
            lax_universes = (uu___126_15500.lax_universes);
            failhard = (uu___126_15500.failhard);
            nosynth = (uu___126_15500.nosynth);
            tc_term = (uu___126_15500.tc_term);
            type_of = (uu___126_15500.type_of);
            universe_of = (uu___126_15500.universe_of);
            check_type_of = (uu___126_15500.check_type_of);
            use_bv_sorts = (uu___126_15500.use_bv_sorts);
            qtbl_name_and_index = (uu___126_15500.qtbl_name_and_index);
            normalized_eff_names = (uu___126_15500.normalized_eff_names);
            proof_ns = (uu___126_15500.proof_ns);
            synth_hook = (uu___126_15500.synth_hook);
            splice = (uu___126_15500.splice);
            is_native_tactic = (uu___126_15500.is_native_tactic);
            identifier_info = (uu___126_15500.identifier_info);
            tc_hooks = (uu___126_15500.tc_hooks);
            dsenv = (uu___126_15500.dsenv);
            dep_graph = (uu___126_15500.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15530 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15530  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15688 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15689 = l1 u t wp e  in
                                l2 u t uu____15688 uu____15689))
                | uu____15690 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15762 = inst_tscheme_with lift_t [u]  in
            match uu____15762 with
            | (uu____15769,lift_t1) ->
                let uu____15771 =
                  let uu____15778 =
                    let uu____15779 =
                      let uu____15794 =
                        let uu____15803 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15810 =
                          let uu____15819 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____15819]  in
                        uu____15803 :: uu____15810  in
                      (lift_t1, uu____15794)  in
                    FStar_Syntax_Syntax.Tm_app uu____15779  in
                  FStar_Syntax_Syntax.mk uu____15778  in
                uu____15771 FStar_Pervasives_Native.None
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
            let uu____15921 = inst_tscheme_with lift_t [u]  in
            match uu____15921 with
            | (uu____15928,lift_t1) ->
                let uu____15930 =
                  let uu____15937 =
                    let uu____15938 =
                      let uu____15953 =
                        let uu____15962 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15969 =
                          let uu____15978 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____15985 =
                            let uu____15994 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____15994]  in
                          uu____15978 :: uu____15985  in
                        uu____15962 :: uu____15969  in
                      (lift_t1, uu____15953)  in
                    FStar_Syntax_Syntax.Tm_app uu____15938  in
                  FStar_Syntax_Syntax.mk uu____15937  in
                uu____15930 FStar_Pervasives_Native.None
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
              let uu____16084 =
                let uu____16085 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16085
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16084  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16089 =
              let uu____16090 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16090  in
            let uu____16091 =
              let uu____16092 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16118 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16118)
                 in
              FStar_Util.dflt "none" uu____16092  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16089
              uu____16091
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16144  ->
                    match uu____16144 with
                    | (e,uu____16152) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16175 =
            match uu____16175 with
            | (i,j) ->
                let uu____16186 = FStar_Ident.lid_equals i j  in
                if uu____16186
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
              let uu____16218 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16228 = FStar_Ident.lid_equals i k  in
                        if uu____16228
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16239 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16239
                                  then []
                                  else
                                    (let uu____16243 =
                                       let uu____16252 =
                                         find_edge order1 (i, k)  in
                                       let uu____16255 =
                                         find_edge order1 (k, j)  in
                                       (uu____16252, uu____16255)  in
                                     match uu____16243 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16270 =
                                           compose_edges e1 e2  in
                                         [uu____16270]
                                     | uu____16271 -> [])))))
                 in
              FStar_List.append order1 uu____16218  in
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
                   let uu____16301 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16303 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16303
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16301
                   then
                     let uu____16308 =
                       let uu____16313 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16313)
                        in
                     let uu____16314 = get_range env  in
                     FStar_Errors.raise_error uu____16308 uu____16314
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16391 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16391
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16440 =
                                              let uu____16449 =
                                                find_edge order2 (i, k)  in
                                              let uu____16452 =
                                                find_edge order2 (j, k)  in
                                              (uu____16449, uu____16452)  in
                                            match uu____16440 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16494,uu____16495)
                                                     ->
                                                     let uu____16502 =
                                                       let uu____16507 =
                                                         let uu____16508 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16508
                                                          in
                                                       let uu____16511 =
                                                         let uu____16512 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16512
                                                          in
                                                       (uu____16507,
                                                         uu____16511)
                                                        in
                                                     (match uu____16502 with
                                                      | (true ,true ) ->
                                                          let uu____16523 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16523
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
                                            | uu____16548 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___127_16621 = env.effects  in
              { decls = (uu___127_16621.decls); order = order2; joins }  in
            let uu___128_16622 = env  in
            {
              solver = (uu___128_16622.solver);
              range = (uu___128_16622.range);
              curmodule = (uu___128_16622.curmodule);
              gamma = (uu___128_16622.gamma);
              gamma_sig = (uu___128_16622.gamma_sig);
              gamma_cache = (uu___128_16622.gamma_cache);
              modules = (uu___128_16622.modules);
              expected_typ = (uu___128_16622.expected_typ);
              sigtab = (uu___128_16622.sigtab);
              is_pattern = (uu___128_16622.is_pattern);
              instantiate_imp = (uu___128_16622.instantiate_imp);
              effects;
              generalize = (uu___128_16622.generalize);
              letrecs = (uu___128_16622.letrecs);
              top_level = (uu___128_16622.top_level);
              check_uvars = (uu___128_16622.check_uvars);
              use_eq = (uu___128_16622.use_eq);
              is_iface = (uu___128_16622.is_iface);
              admit = (uu___128_16622.admit);
              lax = (uu___128_16622.lax);
              lax_universes = (uu___128_16622.lax_universes);
              failhard = (uu___128_16622.failhard);
              nosynth = (uu___128_16622.nosynth);
              tc_term = (uu___128_16622.tc_term);
              type_of = (uu___128_16622.type_of);
              universe_of = (uu___128_16622.universe_of);
              check_type_of = (uu___128_16622.check_type_of);
              use_bv_sorts = (uu___128_16622.use_bv_sorts);
              qtbl_name_and_index = (uu___128_16622.qtbl_name_and_index);
              normalized_eff_names = (uu___128_16622.normalized_eff_names);
              proof_ns = (uu___128_16622.proof_ns);
              synth_hook = (uu___128_16622.synth_hook);
              splice = (uu___128_16622.splice);
              is_native_tactic = (uu___128_16622.is_native_tactic);
              identifier_info = (uu___128_16622.identifier_info);
              tc_hooks = (uu___128_16622.tc_hooks);
              dsenv = (uu___128_16622.dsenv);
              dep_graph = (uu___128_16622.dep_graph)
            }))
      | uu____16623 -> env
  
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
        | uu____16651 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16663 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16663 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16680 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16680 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16699 =
                     let uu____16704 =
                       let uu____16705 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16710 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16717 =
                         let uu____16718 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16718  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16705 uu____16710 uu____16717
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16704)
                      in
                   FStar_Errors.raise_error uu____16699
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16723 =
                     let uu____16732 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16732 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16761  ->
                        fun uu____16762  ->
                          match (uu____16761, uu____16762) with
                          | ((x,uu____16784),(t,uu____16786)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16723
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____16805 =
                     let uu___129_16806 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___129_16806.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___129_16806.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___129_16806.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___129_16806.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____16805
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
          let uu____16836 = effect_decl_opt env effect_name  in
          match uu____16836 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____16869 =
                only_reifiable &&
                  (let uu____16871 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____16871)
                 in
              if uu____16869
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____16887 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____16906 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____16935 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____16935
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____16936 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____16936
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____16948 =
                       let uu____16951 = get_range env  in
                       let uu____16952 =
                         let uu____16959 =
                           let uu____16960 =
                             let uu____16975 =
                               let uu____16984 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____16984; wp]  in
                             (repr, uu____16975)  in
                           FStar_Syntax_Syntax.Tm_app uu____16960  in
                         FStar_Syntax_Syntax.mk uu____16959  in
                       uu____16952 FStar_Pervasives_Native.None uu____16951
                        in
                     FStar_Pervasives_Native.Some uu____16948)
  
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
          let uu____17064 =
            let uu____17069 =
              let uu____17070 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17070
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17069)  in
          let uu____17071 = get_range env  in
          FStar_Errors.raise_error uu____17064 uu____17071  in
        let uu____17072 = effect_repr_aux true env c u_c  in
        match uu____17072 with
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
      | uu____17118 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17129 =
        let uu____17130 = FStar_Syntax_Subst.compress t  in
        uu____17130.FStar_Syntax_Syntax.n  in
      match uu____17129 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17133,c) ->
          is_reifiable_comp env c
      | uu____17151 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___130_17172 = env  in
        {
          solver = (uu___130_17172.solver);
          range = (uu___130_17172.range);
          curmodule = (uu___130_17172.curmodule);
          gamma = (uu___130_17172.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___130_17172.gamma_cache);
          modules = (uu___130_17172.modules);
          expected_typ = (uu___130_17172.expected_typ);
          sigtab = (uu___130_17172.sigtab);
          is_pattern = (uu___130_17172.is_pattern);
          instantiate_imp = (uu___130_17172.instantiate_imp);
          effects = (uu___130_17172.effects);
          generalize = (uu___130_17172.generalize);
          letrecs = (uu___130_17172.letrecs);
          top_level = (uu___130_17172.top_level);
          check_uvars = (uu___130_17172.check_uvars);
          use_eq = (uu___130_17172.use_eq);
          is_iface = (uu___130_17172.is_iface);
          admit = (uu___130_17172.admit);
          lax = (uu___130_17172.lax);
          lax_universes = (uu___130_17172.lax_universes);
          failhard = (uu___130_17172.failhard);
          nosynth = (uu___130_17172.nosynth);
          tc_term = (uu___130_17172.tc_term);
          type_of = (uu___130_17172.type_of);
          universe_of = (uu___130_17172.universe_of);
          check_type_of = (uu___130_17172.check_type_of);
          use_bv_sorts = (uu___130_17172.use_bv_sorts);
          qtbl_name_and_index = (uu___130_17172.qtbl_name_and_index);
          normalized_eff_names = (uu___130_17172.normalized_eff_names);
          proof_ns = (uu___130_17172.proof_ns);
          synth_hook = (uu___130_17172.synth_hook);
          splice = (uu___130_17172.splice);
          is_native_tactic = (uu___130_17172.is_native_tactic);
          identifier_info = (uu___130_17172.identifier_info);
          tc_hooks = (uu___130_17172.tc_hooks);
          dsenv = (uu___130_17172.dsenv);
          dep_graph = (uu___130_17172.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___131_17184 = env  in
      {
        solver = (uu___131_17184.solver);
        range = (uu___131_17184.range);
        curmodule = (uu___131_17184.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___131_17184.gamma_sig);
        gamma_cache = (uu___131_17184.gamma_cache);
        modules = (uu___131_17184.modules);
        expected_typ = (uu___131_17184.expected_typ);
        sigtab = (uu___131_17184.sigtab);
        is_pattern = (uu___131_17184.is_pattern);
        instantiate_imp = (uu___131_17184.instantiate_imp);
        effects = (uu___131_17184.effects);
        generalize = (uu___131_17184.generalize);
        letrecs = (uu___131_17184.letrecs);
        top_level = (uu___131_17184.top_level);
        check_uvars = (uu___131_17184.check_uvars);
        use_eq = (uu___131_17184.use_eq);
        is_iface = (uu___131_17184.is_iface);
        admit = (uu___131_17184.admit);
        lax = (uu___131_17184.lax);
        lax_universes = (uu___131_17184.lax_universes);
        failhard = (uu___131_17184.failhard);
        nosynth = (uu___131_17184.nosynth);
        tc_term = (uu___131_17184.tc_term);
        type_of = (uu___131_17184.type_of);
        universe_of = (uu___131_17184.universe_of);
        check_type_of = (uu___131_17184.check_type_of);
        use_bv_sorts = (uu___131_17184.use_bv_sorts);
        qtbl_name_and_index = (uu___131_17184.qtbl_name_and_index);
        normalized_eff_names = (uu___131_17184.normalized_eff_names);
        proof_ns = (uu___131_17184.proof_ns);
        synth_hook = (uu___131_17184.synth_hook);
        splice = (uu___131_17184.splice);
        is_native_tactic = (uu___131_17184.is_native_tactic);
        identifier_info = (uu___131_17184.identifier_info);
        tc_hooks = (uu___131_17184.tc_hooks);
        dsenv = (uu___131_17184.dsenv);
        dep_graph = (uu___131_17184.dep_graph)
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
            (let uu___132_17239 = env  in
             {
               solver = (uu___132_17239.solver);
               range = (uu___132_17239.range);
               curmodule = (uu___132_17239.curmodule);
               gamma = rest;
               gamma_sig = (uu___132_17239.gamma_sig);
               gamma_cache = (uu___132_17239.gamma_cache);
               modules = (uu___132_17239.modules);
               expected_typ = (uu___132_17239.expected_typ);
               sigtab = (uu___132_17239.sigtab);
               is_pattern = (uu___132_17239.is_pattern);
               instantiate_imp = (uu___132_17239.instantiate_imp);
               effects = (uu___132_17239.effects);
               generalize = (uu___132_17239.generalize);
               letrecs = (uu___132_17239.letrecs);
               top_level = (uu___132_17239.top_level);
               check_uvars = (uu___132_17239.check_uvars);
               use_eq = (uu___132_17239.use_eq);
               is_iface = (uu___132_17239.is_iface);
               admit = (uu___132_17239.admit);
               lax = (uu___132_17239.lax);
               lax_universes = (uu___132_17239.lax_universes);
               failhard = (uu___132_17239.failhard);
               nosynth = (uu___132_17239.nosynth);
               tc_term = (uu___132_17239.tc_term);
               type_of = (uu___132_17239.type_of);
               universe_of = (uu___132_17239.universe_of);
               check_type_of = (uu___132_17239.check_type_of);
               use_bv_sorts = (uu___132_17239.use_bv_sorts);
               qtbl_name_and_index = (uu___132_17239.qtbl_name_and_index);
               normalized_eff_names = (uu___132_17239.normalized_eff_names);
               proof_ns = (uu___132_17239.proof_ns);
               synth_hook = (uu___132_17239.synth_hook);
               splice = (uu___132_17239.splice);
               is_native_tactic = (uu___132_17239.is_native_tactic);
               identifier_info = (uu___132_17239.identifier_info);
               tc_hooks = (uu___132_17239.tc_hooks);
               dsenv = (uu___132_17239.dsenv);
               dep_graph = (uu___132_17239.dep_graph)
             }))
    | uu____17240 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17266  ->
             match uu____17266 with | (x,uu____17272) -> push_bv env1 x) env
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
            let uu___133_17302 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_17302.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_17302.FStar_Syntax_Syntax.index);
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
      (let uu___134_17342 = env  in
       {
         solver = (uu___134_17342.solver);
         range = (uu___134_17342.range);
         curmodule = (uu___134_17342.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___134_17342.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___134_17342.sigtab);
         is_pattern = (uu___134_17342.is_pattern);
         instantiate_imp = (uu___134_17342.instantiate_imp);
         effects = (uu___134_17342.effects);
         generalize = (uu___134_17342.generalize);
         letrecs = (uu___134_17342.letrecs);
         top_level = (uu___134_17342.top_level);
         check_uvars = (uu___134_17342.check_uvars);
         use_eq = (uu___134_17342.use_eq);
         is_iface = (uu___134_17342.is_iface);
         admit = (uu___134_17342.admit);
         lax = (uu___134_17342.lax);
         lax_universes = (uu___134_17342.lax_universes);
         failhard = (uu___134_17342.failhard);
         nosynth = (uu___134_17342.nosynth);
         tc_term = (uu___134_17342.tc_term);
         type_of = (uu___134_17342.type_of);
         universe_of = (uu___134_17342.universe_of);
         check_type_of = (uu___134_17342.check_type_of);
         use_bv_sorts = (uu___134_17342.use_bv_sorts);
         qtbl_name_and_index = (uu___134_17342.qtbl_name_and_index);
         normalized_eff_names = (uu___134_17342.normalized_eff_names);
         proof_ns = (uu___134_17342.proof_ns);
         synth_hook = (uu___134_17342.synth_hook);
         splice = (uu___134_17342.splice);
         is_native_tactic = (uu___134_17342.is_native_tactic);
         identifier_info = (uu___134_17342.identifier_info);
         tc_hooks = (uu___134_17342.tc_hooks);
         dsenv = (uu___134_17342.dsenv);
         dep_graph = (uu___134_17342.dep_graph)
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
        let uu____17384 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17384 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17412 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17412)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___135_17427 = env  in
      {
        solver = (uu___135_17427.solver);
        range = (uu___135_17427.range);
        curmodule = (uu___135_17427.curmodule);
        gamma = (uu___135_17427.gamma);
        gamma_sig = (uu___135_17427.gamma_sig);
        gamma_cache = (uu___135_17427.gamma_cache);
        modules = (uu___135_17427.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___135_17427.sigtab);
        is_pattern = (uu___135_17427.is_pattern);
        instantiate_imp = (uu___135_17427.instantiate_imp);
        effects = (uu___135_17427.effects);
        generalize = (uu___135_17427.generalize);
        letrecs = (uu___135_17427.letrecs);
        top_level = (uu___135_17427.top_level);
        check_uvars = (uu___135_17427.check_uvars);
        use_eq = false;
        is_iface = (uu___135_17427.is_iface);
        admit = (uu___135_17427.admit);
        lax = (uu___135_17427.lax);
        lax_universes = (uu___135_17427.lax_universes);
        failhard = (uu___135_17427.failhard);
        nosynth = (uu___135_17427.nosynth);
        tc_term = (uu___135_17427.tc_term);
        type_of = (uu___135_17427.type_of);
        universe_of = (uu___135_17427.universe_of);
        check_type_of = (uu___135_17427.check_type_of);
        use_bv_sorts = (uu___135_17427.use_bv_sorts);
        qtbl_name_and_index = (uu___135_17427.qtbl_name_and_index);
        normalized_eff_names = (uu___135_17427.normalized_eff_names);
        proof_ns = (uu___135_17427.proof_ns);
        synth_hook = (uu___135_17427.synth_hook);
        splice = (uu___135_17427.splice);
        is_native_tactic = (uu___135_17427.is_native_tactic);
        identifier_info = (uu___135_17427.identifier_info);
        tc_hooks = (uu___135_17427.tc_hooks);
        dsenv = (uu___135_17427.dsenv);
        dep_graph = (uu___135_17427.dep_graph)
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
    let uu____17455 = expected_typ env_  in
    ((let uu___136_17461 = env_  in
      {
        solver = (uu___136_17461.solver);
        range = (uu___136_17461.range);
        curmodule = (uu___136_17461.curmodule);
        gamma = (uu___136_17461.gamma);
        gamma_sig = (uu___136_17461.gamma_sig);
        gamma_cache = (uu___136_17461.gamma_cache);
        modules = (uu___136_17461.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___136_17461.sigtab);
        is_pattern = (uu___136_17461.is_pattern);
        instantiate_imp = (uu___136_17461.instantiate_imp);
        effects = (uu___136_17461.effects);
        generalize = (uu___136_17461.generalize);
        letrecs = (uu___136_17461.letrecs);
        top_level = (uu___136_17461.top_level);
        check_uvars = (uu___136_17461.check_uvars);
        use_eq = false;
        is_iface = (uu___136_17461.is_iface);
        admit = (uu___136_17461.admit);
        lax = (uu___136_17461.lax);
        lax_universes = (uu___136_17461.lax_universes);
        failhard = (uu___136_17461.failhard);
        nosynth = (uu___136_17461.nosynth);
        tc_term = (uu___136_17461.tc_term);
        type_of = (uu___136_17461.type_of);
        universe_of = (uu___136_17461.universe_of);
        check_type_of = (uu___136_17461.check_type_of);
        use_bv_sorts = (uu___136_17461.use_bv_sorts);
        qtbl_name_and_index = (uu___136_17461.qtbl_name_and_index);
        normalized_eff_names = (uu___136_17461.normalized_eff_names);
        proof_ns = (uu___136_17461.proof_ns);
        synth_hook = (uu___136_17461.synth_hook);
        splice = (uu___136_17461.splice);
        is_native_tactic = (uu___136_17461.is_native_tactic);
        identifier_info = (uu___136_17461.identifier_info);
        tc_hooks = (uu___136_17461.tc_hooks);
        dsenv = (uu___136_17461.dsenv);
        dep_graph = (uu___136_17461.dep_graph)
      }), uu____17455)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17471 =
      let uu____17474 = FStar_Ident.id_of_text ""  in [uu____17474]  in
    FStar_Ident.lid_of_ids uu____17471  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17480 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17480
        then
          let uu____17483 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17483 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___137_17510 = env  in
       {
         solver = (uu___137_17510.solver);
         range = (uu___137_17510.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___137_17510.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___137_17510.expected_typ);
         sigtab = (uu___137_17510.sigtab);
         is_pattern = (uu___137_17510.is_pattern);
         instantiate_imp = (uu___137_17510.instantiate_imp);
         effects = (uu___137_17510.effects);
         generalize = (uu___137_17510.generalize);
         letrecs = (uu___137_17510.letrecs);
         top_level = (uu___137_17510.top_level);
         check_uvars = (uu___137_17510.check_uvars);
         use_eq = (uu___137_17510.use_eq);
         is_iface = (uu___137_17510.is_iface);
         admit = (uu___137_17510.admit);
         lax = (uu___137_17510.lax);
         lax_universes = (uu___137_17510.lax_universes);
         failhard = (uu___137_17510.failhard);
         nosynth = (uu___137_17510.nosynth);
         tc_term = (uu___137_17510.tc_term);
         type_of = (uu___137_17510.type_of);
         universe_of = (uu___137_17510.universe_of);
         check_type_of = (uu___137_17510.check_type_of);
         use_bv_sorts = (uu___137_17510.use_bv_sorts);
         qtbl_name_and_index = (uu___137_17510.qtbl_name_and_index);
         normalized_eff_names = (uu___137_17510.normalized_eff_names);
         proof_ns = (uu___137_17510.proof_ns);
         synth_hook = (uu___137_17510.synth_hook);
         splice = (uu___137_17510.splice);
         is_native_tactic = (uu___137_17510.is_native_tactic);
         identifier_info = (uu___137_17510.identifier_info);
         tc_hooks = (uu___137_17510.tc_hooks);
         dsenv = (uu___137_17510.dsenv);
         dep_graph = (uu___137_17510.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17561)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17565,(uu____17566,t)))::tl1
          ->
          let uu____17587 =
            let uu____17590 = FStar_Syntax_Free.uvars t  in
            ext out uu____17590  in
          aux uu____17587 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17593;
            FStar_Syntax_Syntax.index = uu____17594;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17601 =
            let uu____17604 = FStar_Syntax_Free.uvars t  in
            ext out uu____17604  in
          aux uu____17601 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17661)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17665,(uu____17666,t)))::tl1
          ->
          let uu____17687 =
            let uu____17690 = FStar_Syntax_Free.univs t  in
            ext out uu____17690  in
          aux uu____17687 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17693;
            FStar_Syntax_Syntax.index = uu____17694;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17701 =
            let uu____17704 = FStar_Syntax_Free.univs t  in
            ext out uu____17704  in
          aux uu____17701 tl1
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
          let uu____17765 = FStar_Util.set_add uname out  in
          aux uu____17765 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17768,(uu____17769,t)))::tl1
          ->
          let uu____17790 =
            let uu____17793 = FStar_Syntax_Free.univnames t  in
            ext out uu____17793  in
          aux uu____17790 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17796;
            FStar_Syntax_Syntax.index = uu____17797;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17804 =
            let uu____17807 = FStar_Syntax_Free.univnames t  in
            ext out uu____17807  in
          aux uu____17804 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___111_17827  ->
            match uu___111_17827 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____17831 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____17844 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____17854 =
      let uu____17861 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____17861
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____17854 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____17899 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___112_17909  ->
              match uu___112_17909 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____17911 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____17911
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____17914) ->
                  let uu____17931 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____17931))
       in
    FStar_All.pipe_right uu____17899 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___113_17938  ->
    match uu___113_17938 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____17939 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____17959  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18001) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18020,uu____18021) -> false  in
      let uu____18030 =
        FStar_List.tryFind
          (fun uu____18048  ->
             match uu____18048 with | (p,uu____18056) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18030 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18067,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18089 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18089
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___138_18107 = e  in
        {
          solver = (uu___138_18107.solver);
          range = (uu___138_18107.range);
          curmodule = (uu___138_18107.curmodule);
          gamma = (uu___138_18107.gamma);
          gamma_sig = (uu___138_18107.gamma_sig);
          gamma_cache = (uu___138_18107.gamma_cache);
          modules = (uu___138_18107.modules);
          expected_typ = (uu___138_18107.expected_typ);
          sigtab = (uu___138_18107.sigtab);
          is_pattern = (uu___138_18107.is_pattern);
          instantiate_imp = (uu___138_18107.instantiate_imp);
          effects = (uu___138_18107.effects);
          generalize = (uu___138_18107.generalize);
          letrecs = (uu___138_18107.letrecs);
          top_level = (uu___138_18107.top_level);
          check_uvars = (uu___138_18107.check_uvars);
          use_eq = (uu___138_18107.use_eq);
          is_iface = (uu___138_18107.is_iface);
          admit = (uu___138_18107.admit);
          lax = (uu___138_18107.lax);
          lax_universes = (uu___138_18107.lax_universes);
          failhard = (uu___138_18107.failhard);
          nosynth = (uu___138_18107.nosynth);
          tc_term = (uu___138_18107.tc_term);
          type_of = (uu___138_18107.type_of);
          universe_of = (uu___138_18107.universe_of);
          check_type_of = (uu___138_18107.check_type_of);
          use_bv_sorts = (uu___138_18107.use_bv_sorts);
          qtbl_name_and_index = (uu___138_18107.qtbl_name_and_index);
          normalized_eff_names = (uu___138_18107.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___138_18107.synth_hook);
          splice = (uu___138_18107.splice);
          is_native_tactic = (uu___138_18107.is_native_tactic);
          identifier_info = (uu___138_18107.identifier_info);
          tc_hooks = (uu___138_18107.tc_hooks);
          dsenv = (uu___138_18107.dsenv);
          dep_graph = (uu___138_18107.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___139_18147 = e  in
      {
        solver = (uu___139_18147.solver);
        range = (uu___139_18147.range);
        curmodule = (uu___139_18147.curmodule);
        gamma = (uu___139_18147.gamma);
        gamma_sig = (uu___139_18147.gamma_sig);
        gamma_cache = (uu___139_18147.gamma_cache);
        modules = (uu___139_18147.modules);
        expected_typ = (uu___139_18147.expected_typ);
        sigtab = (uu___139_18147.sigtab);
        is_pattern = (uu___139_18147.is_pattern);
        instantiate_imp = (uu___139_18147.instantiate_imp);
        effects = (uu___139_18147.effects);
        generalize = (uu___139_18147.generalize);
        letrecs = (uu___139_18147.letrecs);
        top_level = (uu___139_18147.top_level);
        check_uvars = (uu___139_18147.check_uvars);
        use_eq = (uu___139_18147.use_eq);
        is_iface = (uu___139_18147.is_iface);
        admit = (uu___139_18147.admit);
        lax = (uu___139_18147.lax);
        lax_universes = (uu___139_18147.lax_universes);
        failhard = (uu___139_18147.failhard);
        nosynth = (uu___139_18147.nosynth);
        tc_term = (uu___139_18147.tc_term);
        type_of = (uu___139_18147.type_of);
        universe_of = (uu___139_18147.universe_of);
        check_type_of = (uu___139_18147.check_type_of);
        use_bv_sorts = (uu___139_18147.use_bv_sorts);
        qtbl_name_and_index = (uu___139_18147.qtbl_name_and_index);
        normalized_eff_names = (uu___139_18147.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___139_18147.synth_hook);
        splice = (uu___139_18147.splice);
        is_native_tactic = (uu___139_18147.is_native_tactic);
        identifier_info = (uu___139_18147.identifier_info);
        tc_hooks = (uu___139_18147.tc_hooks);
        dsenv = (uu___139_18147.dsenv);
        dep_graph = (uu___139_18147.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18162 = FStar_Syntax_Free.names t  in
      let uu____18165 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18162 uu____18165
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18186 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18186
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18194 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18194
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18213 =
      match uu____18213 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18229 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18229)
       in
    let uu____18231 =
      let uu____18234 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18234 FStar_List.rev  in
    FStar_All.pipe_right uu____18231 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18249  -> ());
    push = (fun uu____18251  -> ());
    pop = (fun uu____18253  -> ());
    snapshot =
      (fun uu____18255  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18264  -> fun uu____18265  -> ());
    encode_modul = (fun uu____18276  -> fun uu____18277  -> ());
    encode_sig = (fun uu____18280  -> fun uu____18281  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18287 =
             let uu____18294 = FStar_Options.peek ()  in (e, g, uu____18294)
              in
           [uu____18287]);
    solve = (fun uu____18310  -> fun uu____18311  -> fun uu____18312  -> ());
    finish = (fun uu____18318  -> ());
    refresh = (fun uu____18320  -> ())
  } 