open Prims
type sig_binding =
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac 
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
    }
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
  mlift: mlift }
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
    }
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
  
type name_prefix = Prims.string Prims.list
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
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
  dep_graph: FStar_Parser_Dep.deps }
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
  refresh: unit -> unit }
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
    }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
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
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
type implicits =
  (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
    FStar_Range.range,Prims.bool) FStar_Pervasives_Native.tuple5 Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___96_8102  ->
              match uu___96_8102 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8105 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8105  in
                  let uu____8106 =
                    let uu____8107 = FStar_Syntax_Subst.compress y  in
                    uu____8107.FStar_Syntax_Syntax.n  in
                  (match uu____8106 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8111 =
                         let uu___110_8112 = y1  in
                         let uu____8113 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___110_8112.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___110_8112.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8113
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8111
                   | uu____8116 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___111_8128 = env  in
      let uu____8129 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___111_8128.solver);
        range = (uu___111_8128.range);
        curmodule = (uu___111_8128.curmodule);
        gamma = uu____8129;
        gamma_sig = (uu___111_8128.gamma_sig);
        gamma_cache = (uu___111_8128.gamma_cache);
        modules = (uu___111_8128.modules);
        expected_typ = (uu___111_8128.expected_typ);
        sigtab = (uu___111_8128.sigtab);
        is_pattern = (uu___111_8128.is_pattern);
        instantiate_imp = (uu___111_8128.instantiate_imp);
        effects = (uu___111_8128.effects);
        generalize = (uu___111_8128.generalize);
        letrecs = (uu___111_8128.letrecs);
        top_level = (uu___111_8128.top_level);
        check_uvars = (uu___111_8128.check_uvars);
        use_eq = (uu___111_8128.use_eq);
        is_iface = (uu___111_8128.is_iface);
        admit = (uu___111_8128.admit);
        lax = (uu___111_8128.lax);
        lax_universes = (uu___111_8128.lax_universes);
        failhard = (uu___111_8128.failhard);
        nosynth = (uu___111_8128.nosynth);
        tc_term = (uu___111_8128.tc_term);
        type_of = (uu___111_8128.type_of);
        universe_of = (uu___111_8128.universe_of);
        check_type_of = (uu___111_8128.check_type_of);
        use_bv_sorts = (uu___111_8128.use_bv_sorts);
        qtbl_name_and_index = (uu___111_8128.qtbl_name_and_index);
        normalized_eff_names = (uu___111_8128.normalized_eff_names);
        proof_ns = (uu___111_8128.proof_ns);
        synth_hook = (uu___111_8128.synth_hook);
        splice = (uu___111_8128.splice);
        is_native_tactic = (uu___111_8128.is_native_tactic);
        identifier_info = (uu___111_8128.identifier_info);
        tc_hooks = (uu___111_8128.tc_hooks);
        dsenv = (uu___111_8128.dsenv);
        dep_graph = (uu___111_8128.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8136  -> fun uu____8137  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___112_8157 = env  in
      {
        solver = (uu___112_8157.solver);
        range = (uu___112_8157.range);
        curmodule = (uu___112_8157.curmodule);
        gamma = (uu___112_8157.gamma);
        gamma_sig = (uu___112_8157.gamma_sig);
        gamma_cache = (uu___112_8157.gamma_cache);
        modules = (uu___112_8157.modules);
        expected_typ = (uu___112_8157.expected_typ);
        sigtab = (uu___112_8157.sigtab);
        is_pattern = (uu___112_8157.is_pattern);
        instantiate_imp = (uu___112_8157.instantiate_imp);
        effects = (uu___112_8157.effects);
        generalize = (uu___112_8157.generalize);
        letrecs = (uu___112_8157.letrecs);
        top_level = (uu___112_8157.top_level);
        check_uvars = (uu___112_8157.check_uvars);
        use_eq = (uu___112_8157.use_eq);
        is_iface = (uu___112_8157.is_iface);
        admit = (uu___112_8157.admit);
        lax = (uu___112_8157.lax);
        lax_universes = (uu___112_8157.lax_universes);
        failhard = (uu___112_8157.failhard);
        nosynth = (uu___112_8157.nosynth);
        tc_term = (uu___112_8157.tc_term);
        type_of = (uu___112_8157.type_of);
        universe_of = (uu___112_8157.universe_of);
        check_type_of = (uu___112_8157.check_type_of);
        use_bv_sorts = (uu___112_8157.use_bv_sorts);
        qtbl_name_and_index = (uu___112_8157.qtbl_name_and_index);
        normalized_eff_names = (uu___112_8157.normalized_eff_names);
        proof_ns = (uu___112_8157.proof_ns);
        synth_hook = (uu___112_8157.synth_hook);
        splice = (uu___112_8157.splice);
        is_native_tactic = (uu___112_8157.is_native_tactic);
        identifier_info = (uu___112_8157.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___112_8157.dsenv);
        dep_graph = (uu___112_8157.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___113_8168 = e  in
      {
        solver = (uu___113_8168.solver);
        range = (uu___113_8168.range);
        curmodule = (uu___113_8168.curmodule);
        gamma = (uu___113_8168.gamma);
        gamma_sig = (uu___113_8168.gamma_sig);
        gamma_cache = (uu___113_8168.gamma_cache);
        modules = (uu___113_8168.modules);
        expected_typ = (uu___113_8168.expected_typ);
        sigtab = (uu___113_8168.sigtab);
        is_pattern = (uu___113_8168.is_pattern);
        instantiate_imp = (uu___113_8168.instantiate_imp);
        effects = (uu___113_8168.effects);
        generalize = (uu___113_8168.generalize);
        letrecs = (uu___113_8168.letrecs);
        top_level = (uu___113_8168.top_level);
        check_uvars = (uu___113_8168.check_uvars);
        use_eq = (uu___113_8168.use_eq);
        is_iface = (uu___113_8168.is_iface);
        admit = (uu___113_8168.admit);
        lax = (uu___113_8168.lax);
        lax_universes = (uu___113_8168.lax_universes);
        failhard = (uu___113_8168.failhard);
        nosynth = (uu___113_8168.nosynth);
        tc_term = (uu___113_8168.tc_term);
        type_of = (uu___113_8168.type_of);
        universe_of = (uu___113_8168.universe_of);
        check_type_of = (uu___113_8168.check_type_of);
        use_bv_sorts = (uu___113_8168.use_bv_sorts);
        qtbl_name_and_index = (uu___113_8168.qtbl_name_and_index);
        normalized_eff_names = (uu___113_8168.normalized_eff_names);
        proof_ns = (uu___113_8168.proof_ns);
        synth_hook = (uu___113_8168.synth_hook);
        splice = (uu___113_8168.splice);
        is_native_tactic = (uu___113_8168.is_native_tactic);
        identifier_info = (uu___113_8168.identifier_info);
        tc_hooks = (uu___113_8168.tc_hooks);
        dsenv = (uu___113_8168.dsenv);
        dep_graph = g
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun e  -> e.dep_graph 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____8191) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8192,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8193,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8194 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8203 . unit -> 'Auu____8203 FStar_Util.smap =
  fun uu____8210  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8215 . unit -> 'Auu____8215 FStar_Util.smap =
  fun uu____8222  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8332 = new_gamma_cache ()  in
                let uu____8335 = new_sigtab ()  in
                let uu____8338 =
                  let uu____8351 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8351, FStar_Pervasives_Native.None)  in
                let uu____8366 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8369 = FStar_Options.using_facts_from ()  in
                let uu____8370 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8373 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____8332;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8335;
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
                  qtbl_name_and_index = uu____8338;
                  normalized_eff_names = uu____8366;
                  proof_ns = uu____8369;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8409  -> false);
                  identifier_info = uu____8370;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8373;
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
  fun uu____8500  ->
    let uu____8501 = FStar_ST.op_Bang query_indices  in
    match uu____8501 with
    | [] -> failwith "Empty query indices!"
    | uu____8555 ->
        let uu____8564 =
          let uu____8573 =
            let uu____8580 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8580  in
          let uu____8634 = FStar_ST.op_Bang query_indices  in uu____8573 ::
            uu____8634
           in
        FStar_ST.op_Colon_Equals query_indices uu____8564
  
let (pop_query_indices : unit -> unit) =
  fun uu____8731  ->
    let uu____8732 = FStar_ST.op_Bang query_indices  in
    match uu____8732 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____8855  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8885  ->
    match uu____8885 with
    | (l,n1) ->
        let uu____8892 = FStar_ST.op_Bang query_indices  in
        (match uu____8892 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9011 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9030  ->
    let uu____9031 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9031
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9108 =
       let uu____9111 = FStar_ST.op_Bang stack  in env :: uu____9111  in
     FStar_ST.op_Colon_Equals stack uu____9108);
    (let uu___114_9168 = env  in
     let uu____9169 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9172 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9175 =
       let uu____9188 =
         let uu____9191 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9191  in
       let uu____9216 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9188, uu____9216)  in
     let uu____9257 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9260 =
       let uu____9263 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9263  in
     {
       solver = (uu___114_9168.solver);
       range = (uu___114_9168.range);
       curmodule = (uu___114_9168.curmodule);
       gamma = (uu___114_9168.gamma);
       gamma_sig = (uu___114_9168.gamma_sig);
       gamma_cache = uu____9169;
       modules = (uu___114_9168.modules);
       expected_typ = (uu___114_9168.expected_typ);
       sigtab = uu____9172;
       is_pattern = (uu___114_9168.is_pattern);
       instantiate_imp = (uu___114_9168.instantiate_imp);
       effects = (uu___114_9168.effects);
       generalize = (uu___114_9168.generalize);
       letrecs = (uu___114_9168.letrecs);
       top_level = (uu___114_9168.top_level);
       check_uvars = (uu___114_9168.check_uvars);
       use_eq = (uu___114_9168.use_eq);
       is_iface = (uu___114_9168.is_iface);
       admit = (uu___114_9168.admit);
       lax = (uu___114_9168.lax);
       lax_universes = (uu___114_9168.lax_universes);
       failhard = (uu___114_9168.failhard);
       nosynth = (uu___114_9168.nosynth);
       tc_term = (uu___114_9168.tc_term);
       type_of = (uu___114_9168.type_of);
       universe_of = (uu___114_9168.universe_of);
       check_type_of = (uu___114_9168.check_type_of);
       use_bv_sorts = (uu___114_9168.use_bv_sorts);
       qtbl_name_and_index = uu____9175;
       normalized_eff_names = uu____9257;
       proof_ns = (uu___114_9168.proof_ns);
       synth_hook = (uu___114_9168.synth_hook);
       splice = (uu___114_9168.splice);
       is_native_tactic = (uu___114_9168.is_native_tactic);
       identifier_info = uu____9260;
       tc_hooks = (uu___114_9168.tc_hooks);
       dsenv = (uu___114_9168.dsenv);
       dep_graph = (uu___114_9168.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9313  ->
    let uu____9314 = FStar_ST.op_Bang stack  in
    match uu____9314 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9376 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2)
  = fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t =
  (Prims.int,Prims.int,solver_depth_t,Prims.int)
    FStar_Pervasives_Native.tuple4
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t,env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____9448  ->
           let uu____9449 = snapshot_stack env  in
           match uu____9449 with
           | (stack_depth,env1) ->
               let uu____9474 = snapshot_query_indices ()  in
               (match uu____9474 with
                | (query_indices_depth,()) ->
                    let uu____9498 = (env1.solver).snapshot msg  in
                    (match uu____9498 with
                     | (solver_depth,()) ->
                         let uu____9540 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9540 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___115_9586 = env1  in
                                 {
                                   solver = (uu___115_9586.solver);
                                   range = (uu___115_9586.range);
                                   curmodule = (uu___115_9586.curmodule);
                                   gamma = (uu___115_9586.gamma);
                                   gamma_sig = (uu___115_9586.gamma_sig);
                                   gamma_cache = (uu___115_9586.gamma_cache);
                                   modules = (uu___115_9586.modules);
                                   expected_typ =
                                     (uu___115_9586.expected_typ);
                                   sigtab = (uu___115_9586.sigtab);
                                   is_pattern = (uu___115_9586.is_pattern);
                                   instantiate_imp =
                                     (uu___115_9586.instantiate_imp);
                                   effects = (uu___115_9586.effects);
                                   generalize = (uu___115_9586.generalize);
                                   letrecs = (uu___115_9586.letrecs);
                                   top_level = (uu___115_9586.top_level);
                                   check_uvars = (uu___115_9586.check_uvars);
                                   use_eq = (uu___115_9586.use_eq);
                                   is_iface = (uu___115_9586.is_iface);
                                   admit = (uu___115_9586.admit);
                                   lax = (uu___115_9586.lax);
                                   lax_universes =
                                     (uu___115_9586.lax_universes);
                                   failhard = (uu___115_9586.failhard);
                                   nosynth = (uu___115_9586.nosynth);
                                   tc_term = (uu___115_9586.tc_term);
                                   type_of = (uu___115_9586.type_of);
                                   universe_of = (uu___115_9586.universe_of);
                                   check_type_of =
                                     (uu___115_9586.check_type_of);
                                   use_bv_sorts =
                                     (uu___115_9586.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___115_9586.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___115_9586.normalized_eff_names);
                                   proof_ns = (uu___115_9586.proof_ns);
                                   synth_hook = (uu___115_9586.synth_hook);
                                   splice = (uu___115_9586.splice);
                                   is_native_tactic =
                                     (uu___115_9586.is_native_tactic);
                                   identifier_info =
                                     (uu___115_9586.identifier_info);
                                   tc_hooks = (uu___115_9586.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___115_9586.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9617  ->
             let uu____9618 =
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
             match uu____9618 with
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
                             ((let uu____9696 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9696
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9707 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9707
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9734,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9766 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9792  ->
                  match uu____9792 with
                  | (m,uu____9798) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9766 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___116_9806 = env  in
               {
                 solver = (uu___116_9806.solver);
                 range = (uu___116_9806.range);
                 curmodule = (uu___116_9806.curmodule);
                 gamma = (uu___116_9806.gamma);
                 gamma_sig = (uu___116_9806.gamma_sig);
                 gamma_cache = (uu___116_9806.gamma_cache);
                 modules = (uu___116_9806.modules);
                 expected_typ = (uu___116_9806.expected_typ);
                 sigtab = (uu___116_9806.sigtab);
                 is_pattern = (uu___116_9806.is_pattern);
                 instantiate_imp = (uu___116_9806.instantiate_imp);
                 effects = (uu___116_9806.effects);
                 generalize = (uu___116_9806.generalize);
                 letrecs = (uu___116_9806.letrecs);
                 top_level = (uu___116_9806.top_level);
                 check_uvars = (uu___116_9806.check_uvars);
                 use_eq = (uu___116_9806.use_eq);
                 is_iface = (uu___116_9806.is_iface);
                 admit = (uu___116_9806.admit);
                 lax = (uu___116_9806.lax);
                 lax_universes = (uu___116_9806.lax_universes);
                 failhard = (uu___116_9806.failhard);
                 nosynth = (uu___116_9806.nosynth);
                 tc_term = (uu___116_9806.tc_term);
                 type_of = (uu___116_9806.type_of);
                 universe_of = (uu___116_9806.universe_of);
                 check_type_of = (uu___116_9806.check_type_of);
                 use_bv_sorts = (uu___116_9806.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___116_9806.normalized_eff_names);
                 proof_ns = (uu___116_9806.proof_ns);
                 synth_hook = (uu___116_9806.synth_hook);
                 splice = (uu___116_9806.splice);
                 is_native_tactic = (uu___116_9806.is_native_tactic);
                 identifier_info = (uu___116_9806.identifier_info);
                 tc_hooks = (uu___116_9806.tc_hooks);
                 dsenv = (uu___116_9806.dsenv);
                 dep_graph = (uu___116_9806.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9819,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___117_9828 = env  in
               {
                 solver = (uu___117_9828.solver);
                 range = (uu___117_9828.range);
                 curmodule = (uu___117_9828.curmodule);
                 gamma = (uu___117_9828.gamma);
                 gamma_sig = (uu___117_9828.gamma_sig);
                 gamma_cache = (uu___117_9828.gamma_cache);
                 modules = (uu___117_9828.modules);
                 expected_typ = (uu___117_9828.expected_typ);
                 sigtab = (uu___117_9828.sigtab);
                 is_pattern = (uu___117_9828.is_pattern);
                 instantiate_imp = (uu___117_9828.instantiate_imp);
                 effects = (uu___117_9828.effects);
                 generalize = (uu___117_9828.generalize);
                 letrecs = (uu___117_9828.letrecs);
                 top_level = (uu___117_9828.top_level);
                 check_uvars = (uu___117_9828.check_uvars);
                 use_eq = (uu___117_9828.use_eq);
                 is_iface = (uu___117_9828.is_iface);
                 admit = (uu___117_9828.admit);
                 lax = (uu___117_9828.lax);
                 lax_universes = (uu___117_9828.lax_universes);
                 failhard = (uu___117_9828.failhard);
                 nosynth = (uu___117_9828.nosynth);
                 tc_term = (uu___117_9828.tc_term);
                 type_of = (uu___117_9828.type_of);
                 universe_of = (uu___117_9828.universe_of);
                 check_type_of = (uu___117_9828.check_type_of);
                 use_bv_sorts = (uu___117_9828.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___117_9828.normalized_eff_names);
                 proof_ns = (uu___117_9828.proof_ns);
                 synth_hook = (uu___117_9828.synth_hook);
                 splice = (uu___117_9828.splice);
                 is_native_tactic = (uu___117_9828.is_native_tactic);
                 identifier_info = (uu___117_9828.identifier_info);
                 tc_hooks = (uu___117_9828.tc_hooks);
                 dsenv = (uu___117_9828.dsenv);
                 dep_graph = (uu___117_9828.dep_graph)
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
        (let uu___118_9862 = e  in
         {
           solver = (uu___118_9862.solver);
           range = r;
           curmodule = (uu___118_9862.curmodule);
           gamma = (uu___118_9862.gamma);
           gamma_sig = (uu___118_9862.gamma_sig);
           gamma_cache = (uu___118_9862.gamma_cache);
           modules = (uu___118_9862.modules);
           expected_typ = (uu___118_9862.expected_typ);
           sigtab = (uu___118_9862.sigtab);
           is_pattern = (uu___118_9862.is_pattern);
           instantiate_imp = (uu___118_9862.instantiate_imp);
           effects = (uu___118_9862.effects);
           generalize = (uu___118_9862.generalize);
           letrecs = (uu___118_9862.letrecs);
           top_level = (uu___118_9862.top_level);
           check_uvars = (uu___118_9862.check_uvars);
           use_eq = (uu___118_9862.use_eq);
           is_iface = (uu___118_9862.is_iface);
           admit = (uu___118_9862.admit);
           lax = (uu___118_9862.lax);
           lax_universes = (uu___118_9862.lax_universes);
           failhard = (uu___118_9862.failhard);
           nosynth = (uu___118_9862.nosynth);
           tc_term = (uu___118_9862.tc_term);
           type_of = (uu___118_9862.type_of);
           universe_of = (uu___118_9862.universe_of);
           check_type_of = (uu___118_9862.check_type_of);
           use_bv_sorts = (uu___118_9862.use_bv_sorts);
           qtbl_name_and_index = (uu___118_9862.qtbl_name_and_index);
           normalized_eff_names = (uu___118_9862.normalized_eff_names);
           proof_ns = (uu___118_9862.proof_ns);
           synth_hook = (uu___118_9862.synth_hook);
           splice = (uu___118_9862.splice);
           is_native_tactic = (uu___118_9862.is_native_tactic);
           identifier_info = (uu___118_9862.identifier_info);
           tc_hooks = (uu___118_9862.tc_hooks);
           dsenv = (uu___118_9862.dsenv);
           dep_graph = (uu___118_9862.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____9878 =
        let uu____9879 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____9879 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9878
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____9941 =
          let uu____9942 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____9942 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9941
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10004 =
          let uu____10005 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10005 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10004
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10067 =
        let uu____10068 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10068 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10067
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___119_10137 = env  in
      {
        solver = (uu___119_10137.solver);
        range = (uu___119_10137.range);
        curmodule = lid;
        gamma = (uu___119_10137.gamma);
        gamma_sig = (uu___119_10137.gamma_sig);
        gamma_cache = (uu___119_10137.gamma_cache);
        modules = (uu___119_10137.modules);
        expected_typ = (uu___119_10137.expected_typ);
        sigtab = (uu___119_10137.sigtab);
        is_pattern = (uu___119_10137.is_pattern);
        instantiate_imp = (uu___119_10137.instantiate_imp);
        effects = (uu___119_10137.effects);
        generalize = (uu___119_10137.generalize);
        letrecs = (uu___119_10137.letrecs);
        top_level = (uu___119_10137.top_level);
        check_uvars = (uu___119_10137.check_uvars);
        use_eq = (uu___119_10137.use_eq);
        is_iface = (uu___119_10137.is_iface);
        admit = (uu___119_10137.admit);
        lax = (uu___119_10137.lax);
        lax_universes = (uu___119_10137.lax_universes);
        failhard = (uu___119_10137.failhard);
        nosynth = (uu___119_10137.nosynth);
        tc_term = (uu___119_10137.tc_term);
        type_of = (uu___119_10137.type_of);
        universe_of = (uu___119_10137.universe_of);
        check_type_of = (uu___119_10137.check_type_of);
        use_bv_sorts = (uu___119_10137.use_bv_sorts);
        qtbl_name_and_index = (uu___119_10137.qtbl_name_and_index);
        normalized_eff_names = (uu___119_10137.normalized_eff_names);
        proof_ns = (uu___119_10137.proof_ns);
        synth_hook = (uu___119_10137.synth_hook);
        splice = (uu___119_10137.splice);
        is_native_tactic = (uu___119_10137.is_native_tactic);
        identifier_info = (uu___119_10137.identifier_info);
        tc_hooks = (uu___119_10137.tc_hooks);
        dsenv = (uu___119_10137.dsenv);
        dep_graph = (uu___119_10137.dep_graph)
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
      let uu____10164 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10164
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10174 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10174)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10184 =
      let uu____10185 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10185  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10184)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10190  ->
    let uu____10191 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10191
  
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
      | ((formals,t),uu____10247) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10281 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10281)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___97_10297  ->
    match uu___97_10297 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10323  -> new_u_univ ()))
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
      let uu____10342 = inst_tscheme t  in
      match uu____10342 with
      | (us,t1) ->
          let uu____10353 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10353)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10373  ->
          match uu____10373 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10392 =
                         let uu____10393 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10394 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10395 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10396 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10393 uu____10394 uu____10395 uu____10396
                          in
                       failwith uu____10392)
                    else ();
                    (let uu____10398 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10398))
               | uu____10407 ->
                   let uu____10408 =
                     let uu____10409 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10409
                      in
                   failwith uu____10408)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10415 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10421 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10427 -> false
  
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
             | ([],uu____10469) -> Maybe
             | (uu____10476,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10495 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
          let uu____10586 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10586 with
          | FStar_Pervasives_Native.None  ->
              let uu____10609 =
                FStar_Util.find_map env.gamma
                  (fun uu___98_10653  ->
                     match uu___98_10653 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____10692 = FStar_Ident.lid_equals lid l  in
                         if uu____10692
                         then
                           let uu____10713 =
                             let uu____10732 =
                               let uu____10747 = inst_tscheme t  in
                               FStar_Util.Inl uu____10747  in
                             let uu____10762 = FStar_Ident.range_of_lid l  in
                             (uu____10732, uu____10762)  in
                           FStar_Pervasives_Native.Some uu____10713
                         else FStar_Pervasives_Native.None
                     | uu____10814 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____10609
                (fun uu____10852  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___99_10861  ->
                        match uu___99_10861 with
                        | (uu____10864,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____10866);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____10867;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____10868;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____10869;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____10870;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____10890 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____10890
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
                                  uu____10938 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____10945 -> cache t  in
                            let uu____10946 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____10946 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____10952 =
                                   let uu____10953 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____10953)
                                    in
                                 maybe_cache uu____10952)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11021 = find_in_sigtab env lid  in
         match uu____11021 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11108) ->
          add_sigelts env ses
      | uu____11117 ->
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
            | uu____11131 -> ()))

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
        (fun uu___100_11162  ->
           match uu___100_11162 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11180 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11241,lb::[]),uu____11243) ->
            let uu____11250 =
              let uu____11259 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11268 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11259, uu____11268)  in
            FStar_Pervasives_Native.Some uu____11250
        | FStar_Syntax_Syntax.Sig_let ((uu____11281,lbs),uu____11283) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11313 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11325 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11325
                     then
                       let uu____11336 =
                         let uu____11345 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11354 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11345, uu____11354)  in
                       FStar_Pervasives_Native.Some uu____11336
                     else FStar_Pervasives_Native.None)
        | uu____11376 -> FStar_Pervasives_Native.None
  
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
          let uu____11435 =
            let uu____11444 =
              let uu____11449 =
                let uu____11450 =
                  let uu____11453 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11453
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11450)  in
              inst_tscheme1 uu____11449  in
            (uu____11444, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11435
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11475,uu____11476) ->
          let uu____11481 =
            let uu____11490 =
              let uu____11495 =
                let uu____11496 =
                  let uu____11499 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11499  in
                (us, uu____11496)  in
              inst_tscheme1 uu____11495  in
            (uu____11490, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11481
      | uu____11518 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11606 =
          match uu____11606 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11702,uvs,t,uu____11705,uu____11706,uu____11707);
                      FStar_Syntax_Syntax.sigrng = uu____11708;
                      FStar_Syntax_Syntax.sigquals = uu____11709;
                      FStar_Syntax_Syntax.sigmeta = uu____11710;
                      FStar_Syntax_Syntax.sigattrs = uu____11711;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11732 =
                     let uu____11741 = inst_tscheme1 (uvs, t)  in
                     (uu____11741, rng)  in
                   FStar_Pervasives_Native.Some uu____11732
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11765;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11767;
                      FStar_Syntax_Syntax.sigattrs = uu____11768;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11785 =
                     let uu____11786 = in_cur_mod env l  in uu____11786 = Yes
                      in
                   if uu____11785
                   then
                     let uu____11797 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____11797
                      then
                        let uu____11810 =
                          let uu____11819 = inst_tscheme1 (uvs, t)  in
                          (uu____11819, rng)  in
                        FStar_Pervasives_Native.Some uu____11810
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____11850 =
                        let uu____11859 = inst_tscheme1 (uvs, t)  in
                        (uu____11859, rng)  in
                      FStar_Pervasives_Native.Some uu____11850)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11884,uu____11885);
                      FStar_Syntax_Syntax.sigrng = uu____11886;
                      FStar_Syntax_Syntax.sigquals = uu____11887;
                      FStar_Syntax_Syntax.sigmeta = uu____11888;
                      FStar_Syntax_Syntax.sigattrs = uu____11889;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____11928 =
                          let uu____11937 = inst_tscheme1 (uvs, k)  in
                          (uu____11937, rng)  in
                        FStar_Pervasives_Native.Some uu____11928
                    | uu____11958 ->
                        let uu____11959 =
                          let uu____11968 =
                            let uu____11973 =
                              let uu____11974 =
                                let uu____11977 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11977
                                 in
                              (uvs, uu____11974)  in
                            inst_tscheme1 uu____11973  in
                          (uu____11968, rng)  in
                        FStar_Pervasives_Native.Some uu____11959)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12000,uu____12001);
                      FStar_Syntax_Syntax.sigrng = uu____12002;
                      FStar_Syntax_Syntax.sigquals = uu____12003;
                      FStar_Syntax_Syntax.sigmeta = uu____12004;
                      FStar_Syntax_Syntax.sigattrs = uu____12005;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12045 =
                          let uu____12054 = inst_tscheme_with (uvs, k) us  in
                          (uu____12054, rng)  in
                        FStar_Pervasives_Native.Some uu____12045
                    | uu____12075 ->
                        let uu____12076 =
                          let uu____12085 =
                            let uu____12090 =
                              let uu____12091 =
                                let uu____12094 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12094
                                 in
                              (uvs, uu____12091)  in
                            inst_tscheme_with uu____12090 us  in
                          (uu____12085, rng)  in
                        FStar_Pervasives_Native.Some uu____12076)
               | FStar_Util.Inr se ->
                   let uu____12130 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12151;
                          FStar_Syntax_Syntax.sigrng = uu____12152;
                          FStar_Syntax_Syntax.sigquals = uu____12153;
                          FStar_Syntax_Syntax.sigmeta = uu____12154;
                          FStar_Syntax_Syntax.sigattrs = uu____12155;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12170 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12130
                     (FStar_Util.map_option
                        (fun uu____12218  ->
                           match uu____12218 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12249 =
          let uu____12260 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12260 mapper  in
        match uu____12249 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12334 =
              let uu____12345 =
                let uu____12352 =
                  let uu___120_12355 = t  in
                  let uu____12356 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___120_12355.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12356;
                    FStar_Syntax_Syntax.vars =
                      (uu___120_12355.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12352)  in
              (uu____12345, r)  in
            FStar_Pervasives_Native.Some uu____12334
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12403 = lookup_qname env l  in
      match uu____12403 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12422 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12474 = try_lookup_bv env bv  in
      match uu____12474 with
      | FStar_Pervasives_Native.None  ->
          let uu____12489 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12489 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12504 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12505 =
            let uu____12506 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12506  in
          (uu____12504, uu____12505)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12527 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12527 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12593 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12593  in
          let uu____12594 =
            let uu____12603 =
              let uu____12608 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12608)  in
            (uu____12603, r1)  in
          FStar_Pervasives_Native.Some uu____12594
  
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
        let uu____12642 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12642 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12675,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12700 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12700  in
            let uu____12701 =
              let uu____12706 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12706, r1)  in
            FStar_Pervasives_Native.Some uu____12701
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12729 = try_lookup_lid env l  in
      match uu____12729 with
      | FStar_Pervasives_Native.None  ->
          let uu____12756 = name_not_found l  in
          let uu____12761 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12756 uu____12761
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_12801  ->
              match uu___101_12801 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12803 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12822 = lookup_qname env lid  in
      match uu____12822 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12831,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12834;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12836;
              FStar_Syntax_Syntax.sigattrs = uu____12837;_},FStar_Pervasives_Native.None
            ),uu____12838)
          ->
          let uu____12887 =
            let uu____12894 =
              let uu____12895 =
                let uu____12898 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____12898 t  in
              (uvs, uu____12895)  in
            (uu____12894, q)  in
          FStar_Pervasives_Native.Some uu____12887
      | uu____12911 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12932 = lookup_qname env lid  in
      match uu____12932 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12937,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12940;
              FStar_Syntax_Syntax.sigquals = uu____12941;
              FStar_Syntax_Syntax.sigmeta = uu____12942;
              FStar_Syntax_Syntax.sigattrs = uu____12943;_},FStar_Pervasives_Native.None
            ),uu____12944)
          ->
          let uu____12993 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12993 (uvs, t)
      | uu____12998 ->
          let uu____12999 = name_not_found lid  in
          let uu____13004 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12999 uu____13004
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13023 = lookup_qname env lid  in
      match uu____13023 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13028,uvs,t,uu____13031,uu____13032,uu____13033);
              FStar_Syntax_Syntax.sigrng = uu____13034;
              FStar_Syntax_Syntax.sigquals = uu____13035;
              FStar_Syntax_Syntax.sigmeta = uu____13036;
              FStar_Syntax_Syntax.sigattrs = uu____13037;_},FStar_Pervasives_Native.None
            ),uu____13038)
          ->
          let uu____13091 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13091 (uvs, t)
      | uu____13096 ->
          let uu____13097 = name_not_found lid  in
          let uu____13102 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13097 uu____13102
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13123 = lookup_qname env lid  in
      match uu____13123 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13130,uu____13131,uu____13132,uu____13133,uu____13134,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13136;
              FStar_Syntax_Syntax.sigquals = uu____13137;
              FStar_Syntax_Syntax.sigmeta = uu____13138;
              FStar_Syntax_Syntax.sigattrs = uu____13139;_},uu____13140),uu____13141)
          -> (true, dcs)
      | uu____13202 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13215 = lookup_qname env lid  in
      match uu____13215 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13216,uu____13217,uu____13218,l,uu____13220,uu____13221);
              FStar_Syntax_Syntax.sigrng = uu____13222;
              FStar_Syntax_Syntax.sigquals = uu____13223;
              FStar_Syntax_Syntax.sigmeta = uu____13224;
              FStar_Syntax_Syntax.sigattrs = uu____13225;_},uu____13226),uu____13227)
          -> l
      | uu____13282 ->
          let uu____13283 =
            let uu____13284 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13284  in
          failwith uu____13283
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13333)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13384,lbs),uu____13386)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13408 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13408
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13440 -> FStar_Pervasives_Native.None)
        | uu____13445 -> FStar_Pervasives_Native.None
  
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
        let uu____13475 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13475
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13500),uu____13501) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13550 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13571 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13571
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13590 = lookup_qname env ftv  in
      match uu____13590 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13594) ->
          let uu____13639 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13639 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13660,t),r) ->
               let uu____13675 =
                 let uu____13676 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13676 t  in
               FStar_Pervasives_Native.Some uu____13675)
      | uu____13677 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13688 = try_lookup_effect_lid env ftv  in
      match uu____13688 with
      | FStar_Pervasives_Native.None  ->
          let uu____13691 = name_not_found ftv  in
          let uu____13696 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13691 uu____13696
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
        let uu____13719 = lookup_qname env lid0  in
        match uu____13719 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13730);
                FStar_Syntax_Syntax.sigrng = uu____13731;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13733;
                FStar_Syntax_Syntax.sigattrs = uu____13734;_},FStar_Pervasives_Native.None
              ),uu____13735)
            ->
            let lid1 =
              let uu____13789 =
                let uu____13790 = FStar_Ident.range_of_lid lid  in
                let uu____13791 =
                  let uu____13792 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____13792  in
                FStar_Range.set_use_range uu____13790 uu____13791  in
              FStar_Ident.set_lid_range lid uu____13789  in
            let uu____13793 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_13797  ->
                      match uu___102_13797 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13798 -> false))
               in
            if uu____13793
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13812 =
                      let uu____13813 =
                        let uu____13814 = get_range env  in
                        FStar_Range.string_of_range uu____13814  in
                      let uu____13815 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____13816 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13813 uu____13815 uu____13816
                       in
                    failwith uu____13812)
                  in
               match (binders, univs1) with
               | ([],uu____13831) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____13852,uu____13853::uu____13854::uu____13855) ->
                   let uu____13872 =
                     let uu____13873 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____13874 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____13873 uu____13874
                      in
                   failwith uu____13872
               | uu____13881 ->
                   let uu____13894 =
                     let uu____13899 =
                       let uu____13900 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____13900)  in
                     inst_tscheme_with uu____13899 insts  in
                   (match uu____13894 with
                    | (uu____13913,t) ->
                        let t1 =
                          let uu____13916 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____13916 t  in
                        let uu____13917 =
                          let uu____13918 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13918.FStar_Syntax_Syntax.n  in
                        (match uu____13917 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____13949 -> failwith "Impossible")))
        | uu____13956 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____13979 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____13979 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____13992,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____13999 = find1 l2  in
            (match uu____13999 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14006 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14006 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14010 = find1 l  in
            (match uu____14010 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14015 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14015
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14029 = lookup_qname env l1  in
      match uu____14029 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14032;
              FStar_Syntax_Syntax.sigrng = uu____14033;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14035;
              FStar_Syntax_Syntax.sigattrs = uu____14036;_},uu____14037),uu____14038)
          -> q
      | uu____14089 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14110 =
          let uu____14111 =
            let uu____14112 = FStar_Util.string_of_int i  in
            let uu____14113 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14112 uu____14113
             in
          failwith uu____14111  in
        let uu____14114 = lookup_datacon env lid  in
        match uu____14114 with
        | (uu____14119,t) ->
            let uu____14121 =
              let uu____14122 = FStar_Syntax_Subst.compress t  in
              uu____14122.FStar_Syntax_Syntax.n  in
            (match uu____14121 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14126) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14157 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14157
                      FStar_Pervasives_Native.fst)
             | uu____14166 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14177 = lookup_qname env l  in
      match uu____14177 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14178,uu____14179,uu____14180);
              FStar_Syntax_Syntax.sigrng = uu____14181;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14183;
              FStar_Syntax_Syntax.sigattrs = uu____14184;_},uu____14185),uu____14186)
          ->
          FStar_Util.for_some
            (fun uu___103_14239  ->
               match uu___103_14239 with
               | FStar_Syntax_Syntax.Projector uu____14240 -> true
               | uu____14245 -> false) quals
      | uu____14246 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14257 = lookup_qname env lid  in
      match uu____14257 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14258,uu____14259,uu____14260,uu____14261,uu____14262,uu____14263);
              FStar_Syntax_Syntax.sigrng = uu____14264;
              FStar_Syntax_Syntax.sigquals = uu____14265;
              FStar_Syntax_Syntax.sigmeta = uu____14266;
              FStar_Syntax_Syntax.sigattrs = uu____14267;_},uu____14268),uu____14269)
          -> true
      | uu____14324 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14335 = lookup_qname env lid  in
      match uu____14335 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14336,uu____14337,uu____14338,uu____14339,uu____14340,uu____14341);
              FStar_Syntax_Syntax.sigrng = uu____14342;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14344;
              FStar_Syntax_Syntax.sigattrs = uu____14345;_},uu____14346),uu____14347)
          ->
          FStar_Util.for_some
            (fun uu___104_14408  ->
               match uu___104_14408 with
               | FStar_Syntax_Syntax.RecordType uu____14409 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14418 -> true
               | uu____14427 -> false) quals
      | uu____14428 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14434,uu____14435);
            FStar_Syntax_Syntax.sigrng = uu____14436;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14438;
            FStar_Syntax_Syntax.sigattrs = uu____14439;_},uu____14440),uu____14441)
        ->
        FStar_Util.for_some
          (fun uu___105_14498  ->
             match uu___105_14498 with
             | FStar_Syntax_Syntax.Action uu____14499 -> true
             | uu____14500 -> false) quals
    | uu____14501 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14512 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14512
  
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
      let uu____14526 =
        let uu____14527 = FStar_Syntax_Util.un_uinst head1  in
        uu____14527.FStar_Syntax_Syntax.n  in
      match uu____14526 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14531 ->
               true
           | uu____14532 -> false)
      | uu____14533 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14544 = lookup_qname env l  in
      match uu____14544 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14546),uu____14547) ->
          FStar_Util.for_some
            (fun uu___106_14595  ->
               match uu___106_14595 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14596 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14597 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14668 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14684) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14701 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14708 ->
                 FStar_Pervasives_Native.Some true
             | uu____14725 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14726 =
        let uu____14729 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14729 mapper  in
      match uu____14726 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14779 = lookup_qname env lid  in
      match uu____14779 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14780,uu____14781,tps,uu____14783,uu____14784,uu____14785);
              FStar_Syntax_Syntax.sigrng = uu____14786;
              FStar_Syntax_Syntax.sigquals = uu____14787;
              FStar_Syntax_Syntax.sigmeta = uu____14788;
              FStar_Syntax_Syntax.sigattrs = uu____14789;_},uu____14790),uu____14791)
          -> FStar_List.length tps
      | uu____14854 ->
          let uu____14855 = name_not_found lid  in
          let uu____14860 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14855 uu____14860
  
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
           (fun uu____14904  ->
              match uu____14904 with
              | (d,uu____14912) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____14927 = effect_decl_opt env l  in
      match uu____14927 with
      | FStar_Pervasives_Native.None  ->
          let uu____14942 = name_not_found l  in
          let uu____14947 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14942 uu____14947
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____14969  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____14988  ->
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
        let uu____15019 = FStar_Ident.lid_equals l1 l2  in
        if uu____15019
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15027 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15027
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15035 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15088  ->
                        match uu____15088 with
                        | (m1,m2,uu____15101,uu____15102,uu____15103) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15035 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15120 =
                    let uu____15125 =
                      let uu____15126 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15127 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15126
                        uu____15127
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15125)
                     in
                  FStar_Errors.raise_error uu____15120 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15134,uu____15135,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15168 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15168
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
  'Auu____15184 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15184)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15213 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15239  ->
                match uu____15239 with
                | (d,uu____15245) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15213 with
      | FStar_Pervasives_Native.None  ->
          let uu____15256 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15256
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15269 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15269 with
           | (uu____15284,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15300)::(wp,uu____15302)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15338 -> failwith "Impossible"))
  
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
          let uu____15391 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15391
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15393 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15393
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
                  let uu____15401 = get_range env  in
                  let uu____15402 =
                    let uu____15409 =
                      let uu____15410 =
                        let uu____15425 =
                          let uu____15434 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15434]  in
                        (null_wp, uu____15425)  in
                      FStar_Syntax_Syntax.Tm_app uu____15410  in
                    FStar_Syntax_Syntax.mk uu____15409  in
                  uu____15402 FStar_Pervasives_Native.None uu____15401  in
                let uu____15466 =
                  let uu____15467 =
                    let uu____15476 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15476]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15467;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15466))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_15507 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_15507.order);
              joins = (uu___121_15507.joins)
            }  in
          let uu___122_15516 = env  in
          {
            solver = (uu___122_15516.solver);
            range = (uu___122_15516.range);
            curmodule = (uu___122_15516.curmodule);
            gamma = (uu___122_15516.gamma);
            gamma_sig = (uu___122_15516.gamma_sig);
            gamma_cache = (uu___122_15516.gamma_cache);
            modules = (uu___122_15516.modules);
            expected_typ = (uu___122_15516.expected_typ);
            sigtab = (uu___122_15516.sigtab);
            is_pattern = (uu___122_15516.is_pattern);
            instantiate_imp = (uu___122_15516.instantiate_imp);
            effects;
            generalize = (uu___122_15516.generalize);
            letrecs = (uu___122_15516.letrecs);
            top_level = (uu___122_15516.top_level);
            check_uvars = (uu___122_15516.check_uvars);
            use_eq = (uu___122_15516.use_eq);
            is_iface = (uu___122_15516.is_iface);
            admit = (uu___122_15516.admit);
            lax = (uu___122_15516.lax);
            lax_universes = (uu___122_15516.lax_universes);
            failhard = (uu___122_15516.failhard);
            nosynth = (uu___122_15516.nosynth);
            tc_term = (uu___122_15516.tc_term);
            type_of = (uu___122_15516.type_of);
            universe_of = (uu___122_15516.universe_of);
            check_type_of = (uu___122_15516.check_type_of);
            use_bv_sorts = (uu___122_15516.use_bv_sorts);
            qtbl_name_and_index = (uu___122_15516.qtbl_name_and_index);
            normalized_eff_names = (uu___122_15516.normalized_eff_names);
            proof_ns = (uu___122_15516.proof_ns);
            synth_hook = (uu___122_15516.synth_hook);
            splice = (uu___122_15516.splice);
            is_native_tactic = (uu___122_15516.is_native_tactic);
            identifier_info = (uu___122_15516.identifier_info);
            tc_hooks = (uu___122_15516.tc_hooks);
            dsenv = (uu___122_15516.dsenv);
            dep_graph = (uu___122_15516.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15546 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15546  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15704 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15705 = l1 u t wp e  in
                                l2 u t uu____15704 uu____15705))
                | uu____15706 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15778 = inst_tscheme_with lift_t [u]  in
            match uu____15778 with
            | (uu____15785,lift_t1) ->
                let uu____15787 =
                  let uu____15794 =
                    let uu____15795 =
                      let uu____15810 =
                        let uu____15819 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15826 =
                          let uu____15835 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____15835]  in
                        uu____15819 :: uu____15826  in
                      (lift_t1, uu____15810)  in
                    FStar_Syntax_Syntax.Tm_app uu____15795  in
                  FStar_Syntax_Syntax.mk uu____15794  in
                uu____15787 FStar_Pervasives_Native.None
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
            let uu____15937 = inst_tscheme_with lift_t [u]  in
            match uu____15937 with
            | (uu____15944,lift_t1) ->
                let uu____15946 =
                  let uu____15953 =
                    let uu____15954 =
                      let uu____15969 =
                        let uu____15978 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15985 =
                          let uu____15994 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16001 =
                            let uu____16010 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16010]  in
                          uu____15994 :: uu____16001  in
                        uu____15978 :: uu____15985  in
                      (lift_t1, uu____15969)  in
                    FStar_Syntax_Syntax.Tm_app uu____15954  in
                  FStar_Syntax_Syntax.mk uu____15953  in
                uu____15946 FStar_Pervasives_Native.None
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
              let uu____16100 =
                let uu____16101 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16101
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16100  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16105 =
              let uu____16106 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16106  in
            let uu____16107 =
              let uu____16108 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16134 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16134)
                 in
              FStar_Util.dflt "none" uu____16108  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16105
              uu____16107
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16160  ->
                    match uu____16160 with
                    | (e,uu____16168) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16191 =
            match uu____16191 with
            | (i,j) ->
                let uu____16202 = FStar_Ident.lid_equals i j  in
                if uu____16202
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____16234 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16244 = FStar_Ident.lid_equals i k  in
                        if uu____16244
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16255 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16255
                                  then []
                                  else
                                    (let uu____16259 =
                                       let uu____16268 =
                                         find_edge order1 (i, k)  in
                                       let uu____16271 =
                                         find_edge order1 (k, j)  in
                                       (uu____16268, uu____16271)  in
                                     match uu____16259 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16286 =
                                           compose_edges e1 e2  in
                                         [uu____16286]
                                     | uu____16287 -> [])))))
                 in
              FStar_List.append order1 uu____16234  in
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
                   let uu____16317 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16319 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16319
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16317
                   then
                     let uu____16324 =
                       let uu____16329 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16329)
                        in
                     let uu____16330 = get_range env  in
                     FStar_Errors.raise_error uu____16324 uu____16330
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16407 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16407
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16456 =
                                              let uu____16465 =
                                                find_edge order2 (i, k)  in
                                              let uu____16468 =
                                                find_edge order2 (j, k)  in
                                              (uu____16465, uu____16468)  in
                                            match uu____16456 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16510,uu____16511)
                                                     ->
                                                     let uu____16518 =
                                                       let uu____16523 =
                                                         let uu____16524 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16524
                                                          in
                                                       let uu____16527 =
                                                         let uu____16528 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16528
                                                          in
                                                       (uu____16523,
                                                         uu____16527)
                                                        in
                                                     (match uu____16518 with
                                                      | (true ,true ) ->
                                                          let uu____16539 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16539
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
                                            | uu____16564 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___123_16637 = env.effects  in
              { decls = (uu___123_16637.decls); order = order2; joins }  in
            let uu___124_16638 = env  in
            {
              solver = (uu___124_16638.solver);
              range = (uu___124_16638.range);
              curmodule = (uu___124_16638.curmodule);
              gamma = (uu___124_16638.gamma);
              gamma_sig = (uu___124_16638.gamma_sig);
              gamma_cache = (uu___124_16638.gamma_cache);
              modules = (uu___124_16638.modules);
              expected_typ = (uu___124_16638.expected_typ);
              sigtab = (uu___124_16638.sigtab);
              is_pattern = (uu___124_16638.is_pattern);
              instantiate_imp = (uu___124_16638.instantiate_imp);
              effects;
              generalize = (uu___124_16638.generalize);
              letrecs = (uu___124_16638.letrecs);
              top_level = (uu___124_16638.top_level);
              check_uvars = (uu___124_16638.check_uvars);
              use_eq = (uu___124_16638.use_eq);
              is_iface = (uu___124_16638.is_iface);
              admit = (uu___124_16638.admit);
              lax = (uu___124_16638.lax);
              lax_universes = (uu___124_16638.lax_universes);
              failhard = (uu___124_16638.failhard);
              nosynth = (uu___124_16638.nosynth);
              tc_term = (uu___124_16638.tc_term);
              type_of = (uu___124_16638.type_of);
              universe_of = (uu___124_16638.universe_of);
              check_type_of = (uu___124_16638.check_type_of);
              use_bv_sorts = (uu___124_16638.use_bv_sorts);
              qtbl_name_and_index = (uu___124_16638.qtbl_name_and_index);
              normalized_eff_names = (uu___124_16638.normalized_eff_names);
              proof_ns = (uu___124_16638.proof_ns);
              synth_hook = (uu___124_16638.synth_hook);
              splice = (uu___124_16638.splice);
              is_native_tactic = (uu___124_16638.is_native_tactic);
              identifier_info = (uu___124_16638.identifier_info);
              tc_hooks = (uu___124_16638.tc_hooks);
              dsenv = (uu___124_16638.dsenv);
              dep_graph = (uu___124_16638.dep_graph)
            }))
      | uu____16639 -> env
  
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
        | uu____16667 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16679 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16679 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16696 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16696 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16715 =
                     let uu____16720 =
                       let uu____16721 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16726 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16733 =
                         let uu____16734 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16734  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16721 uu____16726 uu____16733
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16720)
                      in
                   FStar_Errors.raise_error uu____16715
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16739 =
                     let uu____16748 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16748 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16777  ->
                        fun uu____16778  ->
                          match (uu____16777, uu____16778) with
                          | ((x,uu____16800),(t,uu____16802)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16739
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____16821 =
                     let uu___125_16822 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_16822.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_16822.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_16822.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_16822.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____16821
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
          let uu____16852 = effect_decl_opt env effect_name  in
          match uu____16852 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____16885 =
                only_reifiable &&
                  (let uu____16887 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____16887)
                 in
              if uu____16885
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____16903 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____16922 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____16951 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____16951
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____16952 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____16952
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____16964 =
                       let uu____16967 = get_range env  in
                       let uu____16968 =
                         let uu____16975 =
                           let uu____16976 =
                             let uu____16991 =
                               let uu____17000 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17000; wp]  in
                             (repr, uu____16991)  in
                           FStar_Syntax_Syntax.Tm_app uu____16976  in
                         FStar_Syntax_Syntax.mk uu____16975  in
                       uu____16968 FStar_Pervasives_Native.None uu____16967
                        in
                     FStar_Pervasives_Native.Some uu____16964)
  
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
          let uu____17080 =
            let uu____17085 =
              let uu____17086 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17086
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17085)  in
          let uu____17087 = get_range env  in
          FStar_Errors.raise_error uu____17080 uu____17087  in
        let uu____17088 = effect_repr_aux true env c u_c  in
        match uu____17088 with
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
      | uu____17134 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17145 =
        let uu____17146 = FStar_Syntax_Subst.compress t  in
        uu____17146.FStar_Syntax_Syntax.n  in
      match uu____17145 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17149,c) ->
          is_reifiable_comp env c
      | uu____17167 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___126_17188 = env  in
        {
          solver = (uu___126_17188.solver);
          range = (uu___126_17188.range);
          curmodule = (uu___126_17188.curmodule);
          gamma = (uu___126_17188.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___126_17188.gamma_cache);
          modules = (uu___126_17188.modules);
          expected_typ = (uu___126_17188.expected_typ);
          sigtab = (uu___126_17188.sigtab);
          is_pattern = (uu___126_17188.is_pattern);
          instantiate_imp = (uu___126_17188.instantiate_imp);
          effects = (uu___126_17188.effects);
          generalize = (uu___126_17188.generalize);
          letrecs = (uu___126_17188.letrecs);
          top_level = (uu___126_17188.top_level);
          check_uvars = (uu___126_17188.check_uvars);
          use_eq = (uu___126_17188.use_eq);
          is_iface = (uu___126_17188.is_iface);
          admit = (uu___126_17188.admit);
          lax = (uu___126_17188.lax);
          lax_universes = (uu___126_17188.lax_universes);
          failhard = (uu___126_17188.failhard);
          nosynth = (uu___126_17188.nosynth);
          tc_term = (uu___126_17188.tc_term);
          type_of = (uu___126_17188.type_of);
          universe_of = (uu___126_17188.universe_of);
          check_type_of = (uu___126_17188.check_type_of);
          use_bv_sorts = (uu___126_17188.use_bv_sorts);
          qtbl_name_and_index = (uu___126_17188.qtbl_name_and_index);
          normalized_eff_names = (uu___126_17188.normalized_eff_names);
          proof_ns = (uu___126_17188.proof_ns);
          synth_hook = (uu___126_17188.synth_hook);
          splice = (uu___126_17188.splice);
          is_native_tactic = (uu___126_17188.is_native_tactic);
          identifier_info = (uu___126_17188.identifier_info);
          tc_hooks = (uu___126_17188.tc_hooks);
          dsenv = (uu___126_17188.dsenv);
          dep_graph = (uu___126_17188.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___127_17200 = env  in
      {
        solver = (uu___127_17200.solver);
        range = (uu___127_17200.range);
        curmodule = (uu___127_17200.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___127_17200.gamma_sig);
        gamma_cache = (uu___127_17200.gamma_cache);
        modules = (uu___127_17200.modules);
        expected_typ = (uu___127_17200.expected_typ);
        sigtab = (uu___127_17200.sigtab);
        is_pattern = (uu___127_17200.is_pattern);
        instantiate_imp = (uu___127_17200.instantiate_imp);
        effects = (uu___127_17200.effects);
        generalize = (uu___127_17200.generalize);
        letrecs = (uu___127_17200.letrecs);
        top_level = (uu___127_17200.top_level);
        check_uvars = (uu___127_17200.check_uvars);
        use_eq = (uu___127_17200.use_eq);
        is_iface = (uu___127_17200.is_iface);
        admit = (uu___127_17200.admit);
        lax = (uu___127_17200.lax);
        lax_universes = (uu___127_17200.lax_universes);
        failhard = (uu___127_17200.failhard);
        nosynth = (uu___127_17200.nosynth);
        tc_term = (uu___127_17200.tc_term);
        type_of = (uu___127_17200.type_of);
        universe_of = (uu___127_17200.universe_of);
        check_type_of = (uu___127_17200.check_type_of);
        use_bv_sorts = (uu___127_17200.use_bv_sorts);
        qtbl_name_and_index = (uu___127_17200.qtbl_name_and_index);
        normalized_eff_names = (uu___127_17200.normalized_eff_names);
        proof_ns = (uu___127_17200.proof_ns);
        synth_hook = (uu___127_17200.synth_hook);
        splice = (uu___127_17200.splice);
        is_native_tactic = (uu___127_17200.is_native_tactic);
        identifier_info = (uu___127_17200.identifier_info);
        tc_hooks = (uu___127_17200.tc_hooks);
        dsenv = (uu___127_17200.dsenv);
        dep_graph = (uu___127_17200.dep_graph)
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
            (let uu___128_17255 = env  in
             {
               solver = (uu___128_17255.solver);
               range = (uu___128_17255.range);
               curmodule = (uu___128_17255.curmodule);
               gamma = rest;
               gamma_sig = (uu___128_17255.gamma_sig);
               gamma_cache = (uu___128_17255.gamma_cache);
               modules = (uu___128_17255.modules);
               expected_typ = (uu___128_17255.expected_typ);
               sigtab = (uu___128_17255.sigtab);
               is_pattern = (uu___128_17255.is_pattern);
               instantiate_imp = (uu___128_17255.instantiate_imp);
               effects = (uu___128_17255.effects);
               generalize = (uu___128_17255.generalize);
               letrecs = (uu___128_17255.letrecs);
               top_level = (uu___128_17255.top_level);
               check_uvars = (uu___128_17255.check_uvars);
               use_eq = (uu___128_17255.use_eq);
               is_iface = (uu___128_17255.is_iface);
               admit = (uu___128_17255.admit);
               lax = (uu___128_17255.lax);
               lax_universes = (uu___128_17255.lax_universes);
               failhard = (uu___128_17255.failhard);
               nosynth = (uu___128_17255.nosynth);
               tc_term = (uu___128_17255.tc_term);
               type_of = (uu___128_17255.type_of);
               universe_of = (uu___128_17255.universe_of);
               check_type_of = (uu___128_17255.check_type_of);
               use_bv_sorts = (uu___128_17255.use_bv_sorts);
               qtbl_name_and_index = (uu___128_17255.qtbl_name_and_index);
               normalized_eff_names = (uu___128_17255.normalized_eff_names);
               proof_ns = (uu___128_17255.proof_ns);
               synth_hook = (uu___128_17255.synth_hook);
               splice = (uu___128_17255.splice);
               is_native_tactic = (uu___128_17255.is_native_tactic);
               identifier_info = (uu___128_17255.identifier_info);
               tc_hooks = (uu___128_17255.tc_hooks);
               dsenv = (uu___128_17255.dsenv);
               dep_graph = (uu___128_17255.dep_graph)
             }))
    | uu____17256 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17282  ->
             match uu____17282 with | (x,uu____17288) -> push_bv env1 x) env
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
            let uu___129_17318 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_17318.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_17318.FStar_Syntax_Syntax.index);
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
      (let uu___130_17358 = env  in
       {
         solver = (uu___130_17358.solver);
         range = (uu___130_17358.range);
         curmodule = (uu___130_17358.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___130_17358.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_17358.sigtab);
         is_pattern = (uu___130_17358.is_pattern);
         instantiate_imp = (uu___130_17358.instantiate_imp);
         effects = (uu___130_17358.effects);
         generalize = (uu___130_17358.generalize);
         letrecs = (uu___130_17358.letrecs);
         top_level = (uu___130_17358.top_level);
         check_uvars = (uu___130_17358.check_uvars);
         use_eq = (uu___130_17358.use_eq);
         is_iface = (uu___130_17358.is_iface);
         admit = (uu___130_17358.admit);
         lax = (uu___130_17358.lax);
         lax_universes = (uu___130_17358.lax_universes);
         failhard = (uu___130_17358.failhard);
         nosynth = (uu___130_17358.nosynth);
         tc_term = (uu___130_17358.tc_term);
         type_of = (uu___130_17358.type_of);
         universe_of = (uu___130_17358.universe_of);
         check_type_of = (uu___130_17358.check_type_of);
         use_bv_sorts = (uu___130_17358.use_bv_sorts);
         qtbl_name_and_index = (uu___130_17358.qtbl_name_and_index);
         normalized_eff_names = (uu___130_17358.normalized_eff_names);
         proof_ns = (uu___130_17358.proof_ns);
         synth_hook = (uu___130_17358.synth_hook);
         splice = (uu___130_17358.splice);
         is_native_tactic = (uu___130_17358.is_native_tactic);
         identifier_info = (uu___130_17358.identifier_info);
         tc_hooks = (uu___130_17358.tc_hooks);
         dsenv = (uu___130_17358.dsenv);
         dep_graph = (uu___130_17358.dep_graph)
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
        let uu____17400 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17400 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17428 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17428)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___131_17443 = env  in
      {
        solver = (uu___131_17443.solver);
        range = (uu___131_17443.range);
        curmodule = (uu___131_17443.curmodule);
        gamma = (uu___131_17443.gamma);
        gamma_sig = (uu___131_17443.gamma_sig);
        gamma_cache = (uu___131_17443.gamma_cache);
        modules = (uu___131_17443.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_17443.sigtab);
        is_pattern = (uu___131_17443.is_pattern);
        instantiate_imp = (uu___131_17443.instantiate_imp);
        effects = (uu___131_17443.effects);
        generalize = (uu___131_17443.generalize);
        letrecs = (uu___131_17443.letrecs);
        top_level = (uu___131_17443.top_level);
        check_uvars = (uu___131_17443.check_uvars);
        use_eq = false;
        is_iface = (uu___131_17443.is_iface);
        admit = (uu___131_17443.admit);
        lax = (uu___131_17443.lax);
        lax_universes = (uu___131_17443.lax_universes);
        failhard = (uu___131_17443.failhard);
        nosynth = (uu___131_17443.nosynth);
        tc_term = (uu___131_17443.tc_term);
        type_of = (uu___131_17443.type_of);
        universe_of = (uu___131_17443.universe_of);
        check_type_of = (uu___131_17443.check_type_of);
        use_bv_sorts = (uu___131_17443.use_bv_sorts);
        qtbl_name_and_index = (uu___131_17443.qtbl_name_and_index);
        normalized_eff_names = (uu___131_17443.normalized_eff_names);
        proof_ns = (uu___131_17443.proof_ns);
        synth_hook = (uu___131_17443.synth_hook);
        splice = (uu___131_17443.splice);
        is_native_tactic = (uu___131_17443.is_native_tactic);
        identifier_info = (uu___131_17443.identifier_info);
        tc_hooks = (uu___131_17443.tc_hooks);
        dsenv = (uu___131_17443.dsenv);
        dep_graph = (uu___131_17443.dep_graph)
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
    let uu____17471 = expected_typ env_  in
    ((let uu___132_17477 = env_  in
      {
        solver = (uu___132_17477.solver);
        range = (uu___132_17477.range);
        curmodule = (uu___132_17477.curmodule);
        gamma = (uu___132_17477.gamma);
        gamma_sig = (uu___132_17477.gamma_sig);
        gamma_cache = (uu___132_17477.gamma_cache);
        modules = (uu___132_17477.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_17477.sigtab);
        is_pattern = (uu___132_17477.is_pattern);
        instantiate_imp = (uu___132_17477.instantiate_imp);
        effects = (uu___132_17477.effects);
        generalize = (uu___132_17477.generalize);
        letrecs = (uu___132_17477.letrecs);
        top_level = (uu___132_17477.top_level);
        check_uvars = (uu___132_17477.check_uvars);
        use_eq = false;
        is_iface = (uu___132_17477.is_iface);
        admit = (uu___132_17477.admit);
        lax = (uu___132_17477.lax);
        lax_universes = (uu___132_17477.lax_universes);
        failhard = (uu___132_17477.failhard);
        nosynth = (uu___132_17477.nosynth);
        tc_term = (uu___132_17477.tc_term);
        type_of = (uu___132_17477.type_of);
        universe_of = (uu___132_17477.universe_of);
        check_type_of = (uu___132_17477.check_type_of);
        use_bv_sorts = (uu___132_17477.use_bv_sorts);
        qtbl_name_and_index = (uu___132_17477.qtbl_name_and_index);
        normalized_eff_names = (uu___132_17477.normalized_eff_names);
        proof_ns = (uu___132_17477.proof_ns);
        synth_hook = (uu___132_17477.synth_hook);
        splice = (uu___132_17477.splice);
        is_native_tactic = (uu___132_17477.is_native_tactic);
        identifier_info = (uu___132_17477.identifier_info);
        tc_hooks = (uu___132_17477.tc_hooks);
        dsenv = (uu___132_17477.dsenv);
        dep_graph = (uu___132_17477.dep_graph)
      }), uu____17471)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17487 =
      let uu____17490 = FStar_Ident.id_of_text ""  in [uu____17490]  in
    FStar_Ident.lid_of_ids uu____17487  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17496 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17496
        then
          let uu____17499 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17499 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___133_17526 = env  in
       {
         solver = (uu___133_17526.solver);
         range = (uu___133_17526.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___133_17526.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_17526.expected_typ);
         sigtab = (uu___133_17526.sigtab);
         is_pattern = (uu___133_17526.is_pattern);
         instantiate_imp = (uu___133_17526.instantiate_imp);
         effects = (uu___133_17526.effects);
         generalize = (uu___133_17526.generalize);
         letrecs = (uu___133_17526.letrecs);
         top_level = (uu___133_17526.top_level);
         check_uvars = (uu___133_17526.check_uvars);
         use_eq = (uu___133_17526.use_eq);
         is_iface = (uu___133_17526.is_iface);
         admit = (uu___133_17526.admit);
         lax = (uu___133_17526.lax);
         lax_universes = (uu___133_17526.lax_universes);
         failhard = (uu___133_17526.failhard);
         nosynth = (uu___133_17526.nosynth);
         tc_term = (uu___133_17526.tc_term);
         type_of = (uu___133_17526.type_of);
         universe_of = (uu___133_17526.universe_of);
         check_type_of = (uu___133_17526.check_type_of);
         use_bv_sorts = (uu___133_17526.use_bv_sorts);
         qtbl_name_and_index = (uu___133_17526.qtbl_name_and_index);
         normalized_eff_names = (uu___133_17526.normalized_eff_names);
         proof_ns = (uu___133_17526.proof_ns);
         synth_hook = (uu___133_17526.synth_hook);
         splice = (uu___133_17526.splice);
         is_native_tactic = (uu___133_17526.is_native_tactic);
         identifier_info = (uu___133_17526.identifier_info);
         tc_hooks = (uu___133_17526.tc_hooks);
         dsenv = (uu___133_17526.dsenv);
         dep_graph = (uu___133_17526.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17577)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17581,(uu____17582,t)))::tl1
          ->
          let uu____17603 =
            let uu____17606 = FStar_Syntax_Free.uvars t  in
            ext out uu____17606  in
          aux uu____17603 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17609;
            FStar_Syntax_Syntax.index = uu____17610;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17617 =
            let uu____17620 = FStar_Syntax_Free.uvars t  in
            ext out uu____17620  in
          aux uu____17617 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17677)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17681,(uu____17682,t)))::tl1
          ->
          let uu____17703 =
            let uu____17706 = FStar_Syntax_Free.univs t  in
            ext out uu____17706  in
          aux uu____17703 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17709;
            FStar_Syntax_Syntax.index = uu____17710;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17717 =
            let uu____17720 = FStar_Syntax_Free.univs t  in
            ext out uu____17720  in
          aux uu____17717 tl1
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
          let uu____17781 = FStar_Util.set_add uname out  in
          aux uu____17781 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17784,(uu____17785,t)))::tl1
          ->
          let uu____17806 =
            let uu____17809 = FStar_Syntax_Free.univnames t  in
            ext out uu____17809  in
          aux uu____17806 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17812;
            FStar_Syntax_Syntax.index = uu____17813;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17820 =
            let uu____17823 = FStar_Syntax_Free.univnames t  in
            ext out uu____17823  in
          aux uu____17820 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___107_17843  ->
            match uu___107_17843 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____17847 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____17860 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____17870 =
      let uu____17877 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____17877
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____17870 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____17915 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___108_17925  ->
              match uu___108_17925 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____17927 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____17927
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____17930) ->
                  let uu____17947 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____17947))
       in
    FStar_All.pipe_right uu____17915 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___109_17954  ->
    match uu___109_17954 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____17955 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____17975  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18017) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18036,uu____18037) -> false  in
      let uu____18046 =
        FStar_List.tryFind
          (fun uu____18064  ->
             match uu____18064 with | (p,uu____18072) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18046 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18083,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18105 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18105
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___134_18123 = e  in
        {
          solver = (uu___134_18123.solver);
          range = (uu___134_18123.range);
          curmodule = (uu___134_18123.curmodule);
          gamma = (uu___134_18123.gamma);
          gamma_sig = (uu___134_18123.gamma_sig);
          gamma_cache = (uu___134_18123.gamma_cache);
          modules = (uu___134_18123.modules);
          expected_typ = (uu___134_18123.expected_typ);
          sigtab = (uu___134_18123.sigtab);
          is_pattern = (uu___134_18123.is_pattern);
          instantiate_imp = (uu___134_18123.instantiate_imp);
          effects = (uu___134_18123.effects);
          generalize = (uu___134_18123.generalize);
          letrecs = (uu___134_18123.letrecs);
          top_level = (uu___134_18123.top_level);
          check_uvars = (uu___134_18123.check_uvars);
          use_eq = (uu___134_18123.use_eq);
          is_iface = (uu___134_18123.is_iface);
          admit = (uu___134_18123.admit);
          lax = (uu___134_18123.lax);
          lax_universes = (uu___134_18123.lax_universes);
          failhard = (uu___134_18123.failhard);
          nosynth = (uu___134_18123.nosynth);
          tc_term = (uu___134_18123.tc_term);
          type_of = (uu___134_18123.type_of);
          universe_of = (uu___134_18123.universe_of);
          check_type_of = (uu___134_18123.check_type_of);
          use_bv_sorts = (uu___134_18123.use_bv_sorts);
          qtbl_name_and_index = (uu___134_18123.qtbl_name_and_index);
          normalized_eff_names = (uu___134_18123.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___134_18123.synth_hook);
          splice = (uu___134_18123.splice);
          is_native_tactic = (uu___134_18123.is_native_tactic);
          identifier_info = (uu___134_18123.identifier_info);
          tc_hooks = (uu___134_18123.tc_hooks);
          dsenv = (uu___134_18123.dsenv);
          dep_graph = (uu___134_18123.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___135_18163 = e  in
      {
        solver = (uu___135_18163.solver);
        range = (uu___135_18163.range);
        curmodule = (uu___135_18163.curmodule);
        gamma = (uu___135_18163.gamma);
        gamma_sig = (uu___135_18163.gamma_sig);
        gamma_cache = (uu___135_18163.gamma_cache);
        modules = (uu___135_18163.modules);
        expected_typ = (uu___135_18163.expected_typ);
        sigtab = (uu___135_18163.sigtab);
        is_pattern = (uu___135_18163.is_pattern);
        instantiate_imp = (uu___135_18163.instantiate_imp);
        effects = (uu___135_18163.effects);
        generalize = (uu___135_18163.generalize);
        letrecs = (uu___135_18163.letrecs);
        top_level = (uu___135_18163.top_level);
        check_uvars = (uu___135_18163.check_uvars);
        use_eq = (uu___135_18163.use_eq);
        is_iface = (uu___135_18163.is_iface);
        admit = (uu___135_18163.admit);
        lax = (uu___135_18163.lax);
        lax_universes = (uu___135_18163.lax_universes);
        failhard = (uu___135_18163.failhard);
        nosynth = (uu___135_18163.nosynth);
        tc_term = (uu___135_18163.tc_term);
        type_of = (uu___135_18163.type_of);
        universe_of = (uu___135_18163.universe_of);
        check_type_of = (uu___135_18163.check_type_of);
        use_bv_sorts = (uu___135_18163.use_bv_sorts);
        qtbl_name_and_index = (uu___135_18163.qtbl_name_and_index);
        normalized_eff_names = (uu___135_18163.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___135_18163.synth_hook);
        splice = (uu___135_18163.splice);
        is_native_tactic = (uu___135_18163.is_native_tactic);
        identifier_info = (uu___135_18163.identifier_info);
        tc_hooks = (uu___135_18163.tc_hooks);
        dsenv = (uu___135_18163.dsenv);
        dep_graph = (uu___135_18163.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18178 = FStar_Syntax_Free.names t  in
      let uu____18181 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18178 uu____18181
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18202 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18202
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18210 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18210
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18229 =
      match uu____18229 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18245 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18245)
       in
    let uu____18247 =
      let uu____18250 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18250 FStar_List.rev  in
    FStar_All.pipe_right uu____18247 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18265  -> ());
    push = (fun uu____18267  -> ());
    pop = (fun uu____18269  -> ());
    snapshot =
      (fun uu____18271  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18280  -> fun uu____18281  -> ());
    encode_modul = (fun uu____18292  -> fun uu____18293  -> ());
    encode_sig = (fun uu____18296  -> fun uu____18297  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18303 =
             let uu____18310 = FStar_Options.peek ()  in (e, g, uu____18310)
              in
           [uu____18303]);
    solve = (fun uu____18326  -> fun uu____18327  -> fun uu____18328  -> ());
    finish = (fun uu____18334  -> ());
    refresh = (fun uu____18336  -> ())
  } 