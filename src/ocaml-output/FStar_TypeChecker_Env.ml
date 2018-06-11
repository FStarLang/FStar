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
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  nosynth: Prims.bool ;
  uvar_subtyping: Prims.bool ;
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
      FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__phase1
  
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__uvar_subtyping
  
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
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
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
type implicits =
  (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
    FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___219_8458  ->
              match uu___219_8458 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8461 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8461  in
                  let uu____8462 =
                    let uu____8463 = FStar_Syntax_Subst.compress y  in
                    uu____8463.FStar_Syntax_Syntax.n  in
                  (match uu____8462 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8467 =
                         let uu___233_8468 = y1  in
                         let uu____8469 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___233_8468.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___233_8468.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8469
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8467
                   | uu____8472 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___234_8484 = env  in
      let uu____8485 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___234_8484.solver);
        range = (uu___234_8484.range);
        curmodule = (uu___234_8484.curmodule);
        gamma = uu____8485;
        gamma_sig = (uu___234_8484.gamma_sig);
        gamma_cache = (uu___234_8484.gamma_cache);
        modules = (uu___234_8484.modules);
        expected_typ = (uu___234_8484.expected_typ);
        sigtab = (uu___234_8484.sigtab);
        is_pattern = (uu___234_8484.is_pattern);
        instantiate_imp = (uu___234_8484.instantiate_imp);
        effects = (uu___234_8484.effects);
        generalize = (uu___234_8484.generalize);
        letrecs = (uu___234_8484.letrecs);
        top_level = (uu___234_8484.top_level);
        check_uvars = (uu___234_8484.check_uvars);
        use_eq = (uu___234_8484.use_eq);
        is_iface = (uu___234_8484.is_iface);
        admit = (uu___234_8484.admit);
        lax = (uu___234_8484.lax);
        lax_universes = (uu___234_8484.lax_universes);
        phase1 = (uu___234_8484.phase1);
        failhard = (uu___234_8484.failhard);
        nosynth = (uu___234_8484.nosynth);
        uvar_subtyping = (uu___234_8484.uvar_subtyping);
        tc_term = (uu___234_8484.tc_term);
        type_of = (uu___234_8484.type_of);
        universe_of = (uu___234_8484.universe_of);
        check_type_of = (uu___234_8484.check_type_of);
        use_bv_sorts = (uu___234_8484.use_bv_sorts);
        qtbl_name_and_index = (uu___234_8484.qtbl_name_and_index);
        normalized_eff_names = (uu___234_8484.normalized_eff_names);
        proof_ns = (uu___234_8484.proof_ns);
        synth_hook = (uu___234_8484.synth_hook);
        splice = (uu___234_8484.splice);
        is_native_tactic = (uu___234_8484.is_native_tactic);
        identifier_info = (uu___234_8484.identifier_info);
        tc_hooks = (uu___234_8484.tc_hooks);
        dsenv = (uu___234_8484.dsenv);
        dep_graph = (uu___234_8484.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8492  -> fun uu____8493  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___235_8513 = env  in
      {
        solver = (uu___235_8513.solver);
        range = (uu___235_8513.range);
        curmodule = (uu___235_8513.curmodule);
        gamma = (uu___235_8513.gamma);
        gamma_sig = (uu___235_8513.gamma_sig);
        gamma_cache = (uu___235_8513.gamma_cache);
        modules = (uu___235_8513.modules);
        expected_typ = (uu___235_8513.expected_typ);
        sigtab = (uu___235_8513.sigtab);
        is_pattern = (uu___235_8513.is_pattern);
        instantiate_imp = (uu___235_8513.instantiate_imp);
        effects = (uu___235_8513.effects);
        generalize = (uu___235_8513.generalize);
        letrecs = (uu___235_8513.letrecs);
        top_level = (uu___235_8513.top_level);
        check_uvars = (uu___235_8513.check_uvars);
        use_eq = (uu___235_8513.use_eq);
        is_iface = (uu___235_8513.is_iface);
        admit = (uu___235_8513.admit);
        lax = (uu___235_8513.lax);
        lax_universes = (uu___235_8513.lax_universes);
        phase1 = (uu___235_8513.phase1);
        failhard = (uu___235_8513.failhard);
        nosynth = (uu___235_8513.nosynth);
        uvar_subtyping = (uu___235_8513.uvar_subtyping);
        tc_term = (uu___235_8513.tc_term);
        type_of = (uu___235_8513.type_of);
        universe_of = (uu___235_8513.universe_of);
        check_type_of = (uu___235_8513.check_type_of);
        use_bv_sorts = (uu___235_8513.use_bv_sorts);
        qtbl_name_and_index = (uu___235_8513.qtbl_name_and_index);
        normalized_eff_names = (uu___235_8513.normalized_eff_names);
        proof_ns = (uu___235_8513.proof_ns);
        synth_hook = (uu___235_8513.synth_hook);
        splice = (uu___235_8513.splice);
        is_native_tactic = (uu___235_8513.is_native_tactic);
        identifier_info = (uu___235_8513.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___235_8513.dsenv);
        dep_graph = (uu___235_8513.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___236_8524 = e  in
      {
        solver = (uu___236_8524.solver);
        range = (uu___236_8524.range);
        curmodule = (uu___236_8524.curmodule);
        gamma = (uu___236_8524.gamma);
        gamma_sig = (uu___236_8524.gamma_sig);
        gamma_cache = (uu___236_8524.gamma_cache);
        modules = (uu___236_8524.modules);
        expected_typ = (uu___236_8524.expected_typ);
        sigtab = (uu___236_8524.sigtab);
        is_pattern = (uu___236_8524.is_pattern);
        instantiate_imp = (uu___236_8524.instantiate_imp);
        effects = (uu___236_8524.effects);
        generalize = (uu___236_8524.generalize);
        letrecs = (uu___236_8524.letrecs);
        top_level = (uu___236_8524.top_level);
        check_uvars = (uu___236_8524.check_uvars);
        use_eq = (uu___236_8524.use_eq);
        is_iface = (uu___236_8524.is_iface);
        admit = (uu___236_8524.admit);
        lax = (uu___236_8524.lax);
        lax_universes = (uu___236_8524.lax_universes);
        phase1 = (uu___236_8524.phase1);
        failhard = (uu___236_8524.failhard);
        nosynth = (uu___236_8524.nosynth);
        uvar_subtyping = (uu___236_8524.uvar_subtyping);
        tc_term = (uu___236_8524.tc_term);
        type_of = (uu___236_8524.type_of);
        universe_of = (uu___236_8524.universe_of);
        check_type_of = (uu___236_8524.check_type_of);
        use_bv_sorts = (uu___236_8524.use_bv_sorts);
        qtbl_name_and_index = (uu___236_8524.qtbl_name_and_index);
        normalized_eff_names = (uu___236_8524.normalized_eff_names);
        proof_ns = (uu___236_8524.proof_ns);
        synth_hook = (uu___236_8524.synth_hook);
        splice = (uu___236_8524.splice);
        is_native_tactic = (uu___236_8524.is_native_tactic);
        identifier_info = (uu___236_8524.identifier_info);
        tc_hooks = (uu___236_8524.tc_hooks);
        dsenv = (uu___236_8524.dsenv);
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
      | (NoDelta ,uu____8547) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8548,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8549,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8550 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8559 . unit -> 'Auu____8559 FStar_Util.smap =
  fun uu____8566  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8571 . unit -> 'Auu____8571 FStar_Util.smap =
  fun uu____8578  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8688 = new_gamma_cache ()  in
                let uu____8691 = new_sigtab ()  in
                let uu____8694 =
                  let uu____8707 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8707, FStar_Pervasives_Native.None)  in
                let uu____8722 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8725 = FStar_Options.using_facts_from ()  in
                let uu____8726 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8729 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____8688;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8691;
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
                  phase1 = false;
                  failhard = false;
                  nosynth = false;
                  uvar_subtyping = true;
                  tc_term;
                  type_of;
                  universe_of;
                  check_type_of;
                  use_bv_sorts = false;
                  qtbl_name_and_index = uu____8694;
                  normalized_eff_names = uu____8722;
                  proof_ns = uu____8725;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8765  -> false);
                  identifier_info = uu____8726;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8729;
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
  fun uu____8856  ->
    let uu____8857 = FStar_ST.op_Bang query_indices  in
    match uu____8857 with
    | [] -> failwith "Empty query indices!"
    | uu____8911 ->
        let uu____8920 =
          let uu____8929 =
            let uu____8936 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8936  in
          let uu____8990 = FStar_ST.op_Bang query_indices  in uu____8929 ::
            uu____8990
           in
        FStar_ST.op_Colon_Equals query_indices uu____8920
  
let (pop_query_indices : unit -> unit) =
  fun uu____9087  ->
    let uu____9088 = FStar_ST.op_Bang query_indices  in
    match uu____9088 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9211  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9241  ->
    match uu____9241 with
    | (l,n1) ->
        let uu____9248 = FStar_ST.op_Bang query_indices  in
        (match uu____9248 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9367 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9386  ->
    let uu____9387 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9387
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9464 =
       let uu____9467 = FStar_ST.op_Bang stack  in env :: uu____9467  in
     FStar_ST.op_Colon_Equals stack uu____9464);
    (let uu___237_9524 = env  in
     let uu____9525 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9528 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9531 =
       let uu____9544 =
         let uu____9547 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9547  in
       let uu____9572 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9544, uu____9572)  in
     let uu____9613 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9616 =
       let uu____9619 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9619  in
     {
       solver = (uu___237_9524.solver);
       range = (uu___237_9524.range);
       curmodule = (uu___237_9524.curmodule);
       gamma = (uu___237_9524.gamma);
       gamma_sig = (uu___237_9524.gamma_sig);
       gamma_cache = uu____9525;
       modules = (uu___237_9524.modules);
       expected_typ = (uu___237_9524.expected_typ);
       sigtab = uu____9528;
       is_pattern = (uu___237_9524.is_pattern);
       instantiate_imp = (uu___237_9524.instantiate_imp);
       effects = (uu___237_9524.effects);
       generalize = (uu___237_9524.generalize);
       letrecs = (uu___237_9524.letrecs);
       top_level = (uu___237_9524.top_level);
       check_uvars = (uu___237_9524.check_uvars);
       use_eq = (uu___237_9524.use_eq);
       is_iface = (uu___237_9524.is_iface);
       admit = (uu___237_9524.admit);
       lax = (uu___237_9524.lax);
       lax_universes = (uu___237_9524.lax_universes);
       phase1 = (uu___237_9524.phase1);
       failhard = (uu___237_9524.failhard);
       nosynth = (uu___237_9524.nosynth);
       uvar_subtyping = (uu___237_9524.uvar_subtyping);
       tc_term = (uu___237_9524.tc_term);
       type_of = (uu___237_9524.type_of);
       universe_of = (uu___237_9524.universe_of);
       check_type_of = (uu___237_9524.check_type_of);
       use_bv_sorts = (uu___237_9524.use_bv_sorts);
       qtbl_name_and_index = uu____9531;
       normalized_eff_names = uu____9613;
       proof_ns = (uu___237_9524.proof_ns);
       synth_hook = (uu___237_9524.synth_hook);
       splice = (uu___237_9524.splice);
       is_native_tactic = (uu___237_9524.is_native_tactic);
       identifier_info = uu____9616;
       tc_hooks = (uu___237_9524.tc_hooks);
       dsenv = (uu___237_9524.dsenv);
       dep_graph = (uu___237_9524.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9669  ->
    let uu____9670 = FStar_ST.op_Bang stack  in
    match uu____9670 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9732 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____9804  ->
           let uu____9805 = snapshot_stack env  in
           match uu____9805 with
           | (stack_depth,env1) ->
               let uu____9830 = snapshot_query_indices ()  in
               (match uu____9830 with
                | (query_indices_depth,()) ->
                    let uu____9854 = (env1.solver).snapshot msg  in
                    (match uu____9854 with
                     | (solver_depth,()) ->
                         let uu____9896 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9896 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___238_9942 = env1  in
                                 {
                                   solver = (uu___238_9942.solver);
                                   range = (uu___238_9942.range);
                                   curmodule = (uu___238_9942.curmodule);
                                   gamma = (uu___238_9942.gamma);
                                   gamma_sig = (uu___238_9942.gamma_sig);
                                   gamma_cache = (uu___238_9942.gamma_cache);
                                   modules = (uu___238_9942.modules);
                                   expected_typ =
                                     (uu___238_9942.expected_typ);
                                   sigtab = (uu___238_9942.sigtab);
                                   is_pattern = (uu___238_9942.is_pattern);
                                   instantiate_imp =
                                     (uu___238_9942.instantiate_imp);
                                   effects = (uu___238_9942.effects);
                                   generalize = (uu___238_9942.generalize);
                                   letrecs = (uu___238_9942.letrecs);
                                   top_level = (uu___238_9942.top_level);
                                   check_uvars = (uu___238_9942.check_uvars);
                                   use_eq = (uu___238_9942.use_eq);
                                   is_iface = (uu___238_9942.is_iface);
                                   admit = (uu___238_9942.admit);
                                   lax = (uu___238_9942.lax);
                                   lax_universes =
                                     (uu___238_9942.lax_universes);
                                   phase1 = (uu___238_9942.phase1);
                                   failhard = (uu___238_9942.failhard);
                                   nosynth = (uu___238_9942.nosynth);
                                   uvar_subtyping =
                                     (uu___238_9942.uvar_subtyping);
                                   tc_term = (uu___238_9942.tc_term);
                                   type_of = (uu___238_9942.type_of);
                                   universe_of = (uu___238_9942.universe_of);
                                   check_type_of =
                                     (uu___238_9942.check_type_of);
                                   use_bv_sorts =
                                     (uu___238_9942.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___238_9942.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___238_9942.normalized_eff_names);
                                   proof_ns = (uu___238_9942.proof_ns);
                                   synth_hook = (uu___238_9942.synth_hook);
                                   splice = (uu___238_9942.splice);
                                   is_native_tactic =
                                     (uu___238_9942.is_native_tactic);
                                   identifier_info =
                                     (uu___238_9942.identifier_info);
                                   tc_hooks = (uu___238_9942.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___238_9942.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9973  ->
             let uu____9974 =
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
             match uu____9974 with
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
                             ((let uu____10100 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____10100
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____10111 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____10111
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____10138,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____10170 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10196  ->
                  match uu____10196 with
                  | (m,uu____10202) -> FStar_Ident.lid_equals l m))
           in
        (match uu____10170 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___239_10210 = env  in
               {
                 solver = (uu___239_10210.solver);
                 range = (uu___239_10210.range);
                 curmodule = (uu___239_10210.curmodule);
                 gamma = (uu___239_10210.gamma);
                 gamma_sig = (uu___239_10210.gamma_sig);
                 gamma_cache = (uu___239_10210.gamma_cache);
                 modules = (uu___239_10210.modules);
                 expected_typ = (uu___239_10210.expected_typ);
                 sigtab = (uu___239_10210.sigtab);
                 is_pattern = (uu___239_10210.is_pattern);
                 instantiate_imp = (uu___239_10210.instantiate_imp);
                 effects = (uu___239_10210.effects);
                 generalize = (uu___239_10210.generalize);
                 letrecs = (uu___239_10210.letrecs);
                 top_level = (uu___239_10210.top_level);
                 check_uvars = (uu___239_10210.check_uvars);
                 use_eq = (uu___239_10210.use_eq);
                 is_iface = (uu___239_10210.is_iface);
                 admit = (uu___239_10210.admit);
                 lax = (uu___239_10210.lax);
                 lax_universes = (uu___239_10210.lax_universes);
                 phase1 = (uu___239_10210.phase1);
                 failhard = (uu___239_10210.failhard);
                 nosynth = (uu___239_10210.nosynth);
                 uvar_subtyping = (uu___239_10210.uvar_subtyping);
                 tc_term = (uu___239_10210.tc_term);
                 type_of = (uu___239_10210.type_of);
                 universe_of = (uu___239_10210.universe_of);
                 check_type_of = (uu___239_10210.check_type_of);
                 use_bv_sorts = (uu___239_10210.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___239_10210.normalized_eff_names);
                 proof_ns = (uu___239_10210.proof_ns);
                 synth_hook = (uu___239_10210.synth_hook);
                 splice = (uu___239_10210.splice);
                 is_native_tactic = (uu___239_10210.is_native_tactic);
                 identifier_info = (uu___239_10210.identifier_info);
                 tc_hooks = (uu___239_10210.tc_hooks);
                 dsenv = (uu___239_10210.dsenv);
                 dep_graph = (uu___239_10210.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____10223,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_10232 = env  in
               {
                 solver = (uu___240_10232.solver);
                 range = (uu___240_10232.range);
                 curmodule = (uu___240_10232.curmodule);
                 gamma = (uu___240_10232.gamma);
                 gamma_sig = (uu___240_10232.gamma_sig);
                 gamma_cache = (uu___240_10232.gamma_cache);
                 modules = (uu___240_10232.modules);
                 expected_typ = (uu___240_10232.expected_typ);
                 sigtab = (uu___240_10232.sigtab);
                 is_pattern = (uu___240_10232.is_pattern);
                 instantiate_imp = (uu___240_10232.instantiate_imp);
                 effects = (uu___240_10232.effects);
                 generalize = (uu___240_10232.generalize);
                 letrecs = (uu___240_10232.letrecs);
                 top_level = (uu___240_10232.top_level);
                 check_uvars = (uu___240_10232.check_uvars);
                 use_eq = (uu___240_10232.use_eq);
                 is_iface = (uu___240_10232.is_iface);
                 admit = (uu___240_10232.admit);
                 lax = (uu___240_10232.lax);
                 lax_universes = (uu___240_10232.lax_universes);
                 phase1 = (uu___240_10232.phase1);
                 failhard = (uu___240_10232.failhard);
                 nosynth = (uu___240_10232.nosynth);
                 uvar_subtyping = (uu___240_10232.uvar_subtyping);
                 tc_term = (uu___240_10232.tc_term);
                 type_of = (uu___240_10232.type_of);
                 universe_of = (uu___240_10232.universe_of);
                 check_type_of = (uu___240_10232.check_type_of);
                 use_bv_sorts = (uu___240_10232.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_10232.normalized_eff_names);
                 proof_ns = (uu___240_10232.proof_ns);
                 synth_hook = (uu___240_10232.synth_hook);
                 splice = (uu___240_10232.splice);
                 is_native_tactic = (uu___240_10232.is_native_tactic);
                 identifier_info = (uu___240_10232.identifier_info);
                 tc_hooks = (uu___240_10232.tc_hooks);
                 dsenv = (uu___240_10232.dsenv);
                 dep_graph = (uu___240_10232.dep_graph)
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
        (let uu___241_10266 = e  in
         {
           solver = (uu___241_10266.solver);
           range = r;
           curmodule = (uu___241_10266.curmodule);
           gamma = (uu___241_10266.gamma);
           gamma_sig = (uu___241_10266.gamma_sig);
           gamma_cache = (uu___241_10266.gamma_cache);
           modules = (uu___241_10266.modules);
           expected_typ = (uu___241_10266.expected_typ);
           sigtab = (uu___241_10266.sigtab);
           is_pattern = (uu___241_10266.is_pattern);
           instantiate_imp = (uu___241_10266.instantiate_imp);
           effects = (uu___241_10266.effects);
           generalize = (uu___241_10266.generalize);
           letrecs = (uu___241_10266.letrecs);
           top_level = (uu___241_10266.top_level);
           check_uvars = (uu___241_10266.check_uvars);
           use_eq = (uu___241_10266.use_eq);
           is_iface = (uu___241_10266.is_iface);
           admit = (uu___241_10266.admit);
           lax = (uu___241_10266.lax);
           lax_universes = (uu___241_10266.lax_universes);
           phase1 = (uu___241_10266.phase1);
           failhard = (uu___241_10266.failhard);
           nosynth = (uu___241_10266.nosynth);
           uvar_subtyping = (uu___241_10266.uvar_subtyping);
           tc_term = (uu___241_10266.tc_term);
           type_of = (uu___241_10266.type_of);
           universe_of = (uu___241_10266.universe_of);
           check_type_of = (uu___241_10266.check_type_of);
           use_bv_sorts = (uu___241_10266.use_bv_sorts);
           qtbl_name_and_index = (uu___241_10266.qtbl_name_and_index);
           normalized_eff_names = (uu___241_10266.normalized_eff_names);
           proof_ns = (uu___241_10266.proof_ns);
           synth_hook = (uu___241_10266.synth_hook);
           splice = (uu___241_10266.splice);
           is_native_tactic = (uu___241_10266.is_native_tactic);
           identifier_info = (uu___241_10266.identifier_info);
           tc_hooks = (uu___241_10266.tc_hooks);
           dsenv = (uu___241_10266.dsenv);
           dep_graph = (uu___241_10266.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10282 =
        let uu____10283 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10283 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10282
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10345 =
          let uu____10346 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10346 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10345
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10408 =
          let uu____10409 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10409 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10408
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10471 =
        let uu____10472 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10472 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10471
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___242_10541 = env  in
      {
        solver = (uu___242_10541.solver);
        range = (uu___242_10541.range);
        curmodule = lid;
        gamma = (uu___242_10541.gamma);
        gamma_sig = (uu___242_10541.gamma_sig);
        gamma_cache = (uu___242_10541.gamma_cache);
        modules = (uu___242_10541.modules);
        expected_typ = (uu___242_10541.expected_typ);
        sigtab = (uu___242_10541.sigtab);
        is_pattern = (uu___242_10541.is_pattern);
        instantiate_imp = (uu___242_10541.instantiate_imp);
        effects = (uu___242_10541.effects);
        generalize = (uu___242_10541.generalize);
        letrecs = (uu___242_10541.letrecs);
        top_level = (uu___242_10541.top_level);
        check_uvars = (uu___242_10541.check_uvars);
        use_eq = (uu___242_10541.use_eq);
        is_iface = (uu___242_10541.is_iface);
        admit = (uu___242_10541.admit);
        lax = (uu___242_10541.lax);
        lax_universes = (uu___242_10541.lax_universes);
        phase1 = (uu___242_10541.phase1);
        failhard = (uu___242_10541.failhard);
        nosynth = (uu___242_10541.nosynth);
        uvar_subtyping = (uu___242_10541.uvar_subtyping);
        tc_term = (uu___242_10541.tc_term);
        type_of = (uu___242_10541.type_of);
        universe_of = (uu___242_10541.universe_of);
        check_type_of = (uu___242_10541.check_type_of);
        use_bv_sorts = (uu___242_10541.use_bv_sorts);
        qtbl_name_and_index = (uu___242_10541.qtbl_name_and_index);
        normalized_eff_names = (uu___242_10541.normalized_eff_names);
        proof_ns = (uu___242_10541.proof_ns);
        synth_hook = (uu___242_10541.synth_hook);
        splice = (uu___242_10541.splice);
        is_native_tactic = (uu___242_10541.is_native_tactic);
        identifier_info = (uu___242_10541.identifier_info);
        tc_hooks = (uu___242_10541.tc_hooks);
        dsenv = (uu___242_10541.dsenv);
        dep_graph = (uu___242_10541.dep_graph)
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
      let uu____10568 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10568
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10578 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10578)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10588 =
      let uu____10589 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10589  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10588)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10594  ->
    let uu____10595 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10595
  
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
      | ((formals,t),uu____10651) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10685 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10685)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___220_10701  ->
    match uu___220_10701 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10727  -> new_u_univ ()))
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
      let uu____10746 = inst_tscheme t  in
      match uu____10746 with
      | (us,t1) ->
          let uu____10757 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10757)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10777  ->
          match uu____10777 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10796 =
                         let uu____10797 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10798 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10799 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10800 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10797 uu____10798 uu____10799 uu____10800
                          in
                       failwith uu____10796)
                    else ();
                    (let uu____10802 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10802))
               | uu____10811 ->
                   let uu____10812 =
                     let uu____10813 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10813
                      in
                   failwith uu____10812)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10819 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10825 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10831 -> false
  
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
             | ([],uu____10873) -> Maybe
             | (uu____10880,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10899 -> No  in
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
          let uu____10990 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10990 with
          | FStar_Pervasives_Native.None  ->
              let uu____11013 =
                FStar_Util.find_map env.gamma
                  (fun uu___221_11057  ->
                     match uu___221_11057 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11096 = FStar_Ident.lid_equals lid l  in
                         if uu____11096
                         then
                           let uu____11117 =
                             let uu____11136 =
                               let uu____11151 = inst_tscheme t  in
                               FStar_Util.Inl uu____11151  in
                             let uu____11166 = FStar_Ident.range_of_lid l  in
                             (uu____11136, uu____11166)  in
                           FStar_Pervasives_Native.Some uu____11117
                         else FStar_Pervasives_Native.None
                     | uu____11218 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11013
                (fun uu____11256  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___222_11265  ->
                        match uu___222_11265 with
                        | (uu____11268,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11270);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11271;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11272;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11273;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11274;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11294 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11294
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
                                  uu____11342 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11349 -> cache t  in
                            let uu____11350 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11350 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11356 =
                                   let uu____11357 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11357)
                                    in
                                 maybe_cache uu____11356)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11425 = find_in_sigtab env lid  in
         match uu____11425 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11512) ->
          add_sigelts env ses
      | uu____11521 ->
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
            | uu____11535 -> ()))

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
        (fun uu___223_11566  ->
           match uu___223_11566 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11584 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11645,lb::[]),uu____11647) ->
            let uu____11654 =
              let uu____11663 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11672 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11663, uu____11672)  in
            FStar_Pervasives_Native.Some uu____11654
        | FStar_Syntax_Syntax.Sig_let ((uu____11685,lbs),uu____11687) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11717 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11729 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11729
                     then
                       let uu____11740 =
                         let uu____11749 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11758 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11749, uu____11758)  in
                       FStar_Pervasives_Native.Some uu____11740
                     else FStar_Pervasives_Native.None)
        | uu____11780 -> FStar_Pervasives_Native.None
  
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
          let uu____11839 =
            let uu____11848 =
              let uu____11853 =
                let uu____11854 =
                  let uu____11857 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11857
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11854)  in
              inst_tscheme1 uu____11853  in
            (uu____11848, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11839
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11879,uu____11880) ->
          let uu____11885 =
            let uu____11894 =
              let uu____11899 =
                let uu____11900 =
                  let uu____11903 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11903  in
                (us, uu____11900)  in
              inst_tscheme1 uu____11899  in
            (uu____11894, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11885
      | uu____11922 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12010 =
          match uu____12010 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12106,uvs,t,uu____12109,uu____12110,uu____12111);
                      FStar_Syntax_Syntax.sigrng = uu____12112;
                      FStar_Syntax_Syntax.sigquals = uu____12113;
                      FStar_Syntax_Syntax.sigmeta = uu____12114;
                      FStar_Syntax_Syntax.sigattrs = uu____12115;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12136 =
                     let uu____12145 = inst_tscheme1 (uvs, t)  in
                     (uu____12145, rng)  in
                   FStar_Pervasives_Native.Some uu____12136
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12169;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12171;
                      FStar_Syntax_Syntax.sigattrs = uu____12172;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12189 =
                     let uu____12190 = in_cur_mod env l  in uu____12190 = Yes
                      in
                   if uu____12189
                   then
                     let uu____12201 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12201
                      then
                        let uu____12214 =
                          let uu____12223 = inst_tscheme1 (uvs, t)  in
                          (uu____12223, rng)  in
                        FStar_Pervasives_Native.Some uu____12214
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12254 =
                        let uu____12263 = inst_tscheme1 (uvs, t)  in
                        (uu____12263, rng)  in
                      FStar_Pervasives_Native.Some uu____12254)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12288,uu____12289);
                      FStar_Syntax_Syntax.sigrng = uu____12290;
                      FStar_Syntax_Syntax.sigquals = uu____12291;
                      FStar_Syntax_Syntax.sigmeta = uu____12292;
                      FStar_Syntax_Syntax.sigattrs = uu____12293;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12332 =
                          let uu____12341 = inst_tscheme1 (uvs, k)  in
                          (uu____12341, rng)  in
                        FStar_Pervasives_Native.Some uu____12332
                    | uu____12362 ->
                        let uu____12363 =
                          let uu____12372 =
                            let uu____12377 =
                              let uu____12378 =
                                let uu____12381 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12381
                                 in
                              (uvs, uu____12378)  in
                            inst_tscheme1 uu____12377  in
                          (uu____12372, rng)  in
                        FStar_Pervasives_Native.Some uu____12363)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12404,uu____12405);
                      FStar_Syntax_Syntax.sigrng = uu____12406;
                      FStar_Syntax_Syntax.sigquals = uu____12407;
                      FStar_Syntax_Syntax.sigmeta = uu____12408;
                      FStar_Syntax_Syntax.sigattrs = uu____12409;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12449 =
                          let uu____12458 = inst_tscheme_with (uvs, k) us  in
                          (uu____12458, rng)  in
                        FStar_Pervasives_Native.Some uu____12449
                    | uu____12479 ->
                        let uu____12480 =
                          let uu____12489 =
                            let uu____12494 =
                              let uu____12495 =
                                let uu____12498 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12498
                                 in
                              (uvs, uu____12495)  in
                            inst_tscheme_with uu____12494 us  in
                          (uu____12489, rng)  in
                        FStar_Pervasives_Native.Some uu____12480)
               | FStar_Util.Inr se ->
                   let uu____12534 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12555;
                          FStar_Syntax_Syntax.sigrng = uu____12556;
                          FStar_Syntax_Syntax.sigquals = uu____12557;
                          FStar_Syntax_Syntax.sigmeta = uu____12558;
                          FStar_Syntax_Syntax.sigattrs = uu____12559;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12574 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12534
                     (FStar_Util.map_option
                        (fun uu____12622  ->
                           match uu____12622 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12653 =
          let uu____12664 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12664 mapper  in
        match uu____12653 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12738 =
              let uu____12749 =
                let uu____12756 =
                  let uu___243_12759 = t  in
                  let uu____12760 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___243_12759.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12760;
                    FStar_Syntax_Syntax.vars =
                      (uu___243_12759.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12756)  in
              (uu____12749, r)  in
            FStar_Pervasives_Native.Some uu____12738
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12807 = lookup_qname env l  in
      match uu____12807 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12826 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12878 = try_lookup_bv env bv  in
      match uu____12878 with
      | FStar_Pervasives_Native.None  ->
          let uu____12893 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12893 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12908 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12909 =
            let uu____12910 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12910  in
          (uu____12908, uu____12909)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12931 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12931 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12997 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12997  in
          let uu____12998 =
            let uu____13007 =
              let uu____13012 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13012)  in
            (uu____13007, r1)  in
          FStar_Pervasives_Native.Some uu____12998
  
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
        let uu____13046 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13046 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13079,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13104 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13104  in
            let uu____13105 =
              let uu____13110 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13110, r1)  in
            FStar_Pervasives_Native.Some uu____13105
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13133 = try_lookup_lid env l  in
      match uu____13133 with
      | FStar_Pervasives_Native.None  ->
          let uu____13160 = name_not_found l  in
          let uu____13165 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13160 uu____13165
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___224_13205  ->
              match uu___224_13205 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13207 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13226 = lookup_qname env lid  in
      match uu____13226 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13235,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13238;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13240;
              FStar_Syntax_Syntax.sigattrs = uu____13241;_},FStar_Pervasives_Native.None
            ),uu____13242)
          ->
          let uu____13291 =
            let uu____13298 =
              let uu____13299 =
                let uu____13302 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13302 t  in
              (uvs, uu____13299)  in
            (uu____13298, q)  in
          FStar_Pervasives_Native.Some uu____13291
      | uu____13315 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13336 = lookup_qname env lid  in
      match uu____13336 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13341,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13344;
              FStar_Syntax_Syntax.sigquals = uu____13345;
              FStar_Syntax_Syntax.sigmeta = uu____13346;
              FStar_Syntax_Syntax.sigattrs = uu____13347;_},FStar_Pervasives_Native.None
            ),uu____13348)
          ->
          let uu____13397 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13397 (uvs, t)
      | uu____13402 ->
          let uu____13403 = name_not_found lid  in
          let uu____13408 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13403 uu____13408
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13427 = lookup_qname env lid  in
      match uu____13427 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13432,uvs,t,uu____13435,uu____13436,uu____13437);
              FStar_Syntax_Syntax.sigrng = uu____13438;
              FStar_Syntax_Syntax.sigquals = uu____13439;
              FStar_Syntax_Syntax.sigmeta = uu____13440;
              FStar_Syntax_Syntax.sigattrs = uu____13441;_},FStar_Pervasives_Native.None
            ),uu____13442)
          ->
          let uu____13495 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13495 (uvs, t)
      | uu____13500 ->
          let uu____13501 = name_not_found lid  in
          let uu____13506 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13501 uu____13506
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13527 = lookup_qname env lid  in
      match uu____13527 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13534,uu____13535,uu____13536,uu____13537,uu____13538,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13540;
              FStar_Syntax_Syntax.sigquals = uu____13541;
              FStar_Syntax_Syntax.sigmeta = uu____13542;
              FStar_Syntax_Syntax.sigattrs = uu____13543;_},uu____13544),uu____13545)
          -> (true, dcs)
      | uu____13606 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13619 = lookup_qname env lid  in
      match uu____13619 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13620,uu____13621,uu____13622,l,uu____13624,uu____13625);
              FStar_Syntax_Syntax.sigrng = uu____13626;
              FStar_Syntax_Syntax.sigquals = uu____13627;
              FStar_Syntax_Syntax.sigmeta = uu____13628;
              FStar_Syntax_Syntax.sigattrs = uu____13629;_},uu____13630),uu____13631)
          -> l
      | uu____13686 ->
          let uu____13687 =
            let uu____13688 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13688  in
          failwith uu____13687
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13737)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13788,lbs),uu____13790)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13812 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13812
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13844 -> FStar_Pervasives_Native.None)
        | uu____13849 -> FStar_Pervasives_Native.None
  
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
        let uu____13879 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13879
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13904),uu____13905) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13954 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13975 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13975
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13994 = lookup_qname env ftv  in
      match uu____13994 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13998) ->
          let uu____14043 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14043 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14064,t),r) ->
               let uu____14079 =
                 let uu____14080 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14080 t  in
               FStar_Pervasives_Native.Some uu____14079)
      | uu____14081 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14092 = try_lookup_effect_lid env ftv  in
      match uu____14092 with
      | FStar_Pervasives_Native.None  ->
          let uu____14095 = name_not_found ftv  in
          let uu____14100 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14095 uu____14100
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
        let uu____14123 = lookup_qname env lid0  in
        match uu____14123 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14134);
                FStar_Syntax_Syntax.sigrng = uu____14135;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14137;
                FStar_Syntax_Syntax.sigattrs = uu____14138;_},FStar_Pervasives_Native.None
              ),uu____14139)
            ->
            let lid1 =
              let uu____14193 =
                let uu____14194 = FStar_Ident.range_of_lid lid  in
                let uu____14195 =
                  let uu____14196 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14196  in
                FStar_Range.set_use_range uu____14194 uu____14195  in
              FStar_Ident.set_lid_range lid uu____14193  in
            let uu____14197 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___225_14201  ->
                      match uu___225_14201 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14202 -> false))
               in
            if uu____14197
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14216 =
                      let uu____14217 =
                        let uu____14218 = get_range env  in
                        FStar_Range.string_of_range uu____14218  in
                      let uu____14219 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14220 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14217 uu____14219 uu____14220
                       in
                    failwith uu____14216)
                  in
               match (binders, univs1) with
               | ([],uu____14235) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14256,uu____14257::uu____14258::uu____14259) ->
                   let uu____14276 =
                     let uu____14277 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14278 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14277 uu____14278
                      in
                   failwith uu____14276
               | uu____14285 ->
                   let uu____14298 =
                     let uu____14303 =
                       let uu____14304 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14304)  in
                     inst_tscheme_with uu____14303 insts  in
                   (match uu____14298 with
                    | (uu____14317,t) ->
                        let t1 =
                          let uu____14320 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14320 t  in
                        let uu____14321 =
                          let uu____14322 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14322.FStar_Syntax_Syntax.n  in
                        (match uu____14321 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14353 -> failwith "Impossible")))
        | uu____14360 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14383 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14383 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14396,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14403 = find1 l2  in
            (match uu____14403 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14410 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14410 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14414 = find1 l  in
            (match uu____14414 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14419 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14419
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14433 = lookup_qname env l1  in
      match uu____14433 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14436;
              FStar_Syntax_Syntax.sigrng = uu____14437;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14439;
              FStar_Syntax_Syntax.sigattrs = uu____14440;_},uu____14441),uu____14442)
          -> q
      | uu____14493 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14514 =
          let uu____14515 =
            let uu____14516 = FStar_Util.string_of_int i  in
            let uu____14517 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14516 uu____14517
             in
          failwith uu____14515  in
        let uu____14518 = lookup_datacon env lid  in
        match uu____14518 with
        | (uu____14523,t) ->
            let uu____14525 =
              let uu____14526 = FStar_Syntax_Subst.compress t  in
              uu____14526.FStar_Syntax_Syntax.n  in
            (match uu____14525 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14530) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14561 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14561
                      FStar_Pervasives_Native.fst)
             | uu____14570 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14581 = lookup_qname env l  in
      match uu____14581 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14582,uu____14583,uu____14584);
              FStar_Syntax_Syntax.sigrng = uu____14585;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14587;
              FStar_Syntax_Syntax.sigattrs = uu____14588;_},uu____14589),uu____14590)
          ->
          FStar_Util.for_some
            (fun uu___226_14643  ->
               match uu___226_14643 with
               | FStar_Syntax_Syntax.Projector uu____14644 -> true
               | uu____14649 -> false) quals
      | uu____14650 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14661 = lookup_qname env lid  in
      match uu____14661 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14662,uu____14663,uu____14664,uu____14665,uu____14666,uu____14667);
              FStar_Syntax_Syntax.sigrng = uu____14668;
              FStar_Syntax_Syntax.sigquals = uu____14669;
              FStar_Syntax_Syntax.sigmeta = uu____14670;
              FStar_Syntax_Syntax.sigattrs = uu____14671;_},uu____14672),uu____14673)
          -> true
      | uu____14728 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14739 = lookup_qname env lid  in
      match uu____14739 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14740,uu____14741,uu____14742,uu____14743,uu____14744,uu____14745);
              FStar_Syntax_Syntax.sigrng = uu____14746;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14748;
              FStar_Syntax_Syntax.sigattrs = uu____14749;_},uu____14750),uu____14751)
          ->
          FStar_Util.for_some
            (fun uu___227_14812  ->
               match uu___227_14812 with
               | FStar_Syntax_Syntax.RecordType uu____14813 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14822 -> true
               | uu____14831 -> false) quals
      | uu____14832 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14838,uu____14839);
            FStar_Syntax_Syntax.sigrng = uu____14840;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14842;
            FStar_Syntax_Syntax.sigattrs = uu____14843;_},uu____14844),uu____14845)
        ->
        FStar_Util.for_some
          (fun uu___228_14902  ->
             match uu___228_14902 with
             | FStar_Syntax_Syntax.Action uu____14903 -> true
             | uu____14904 -> false) quals
    | uu____14905 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14916 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14916
  
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
      let uu____14930 =
        let uu____14931 = FStar_Syntax_Util.un_uinst head1  in
        uu____14931.FStar_Syntax_Syntax.n  in
      match uu____14930 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14935 ->
               true
           | uu____14936 -> false)
      | uu____14937 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14948 = lookup_qname env l  in
      match uu____14948 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14950),uu____14951) ->
          FStar_Util.for_some
            (fun uu___229_14999  ->
               match uu___229_14999 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____15000 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____15001 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15072 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15088) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15105 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15112 ->
                 FStar_Pervasives_Native.Some true
             | uu____15129 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15130 =
        let uu____15133 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15133 mapper  in
      match uu____15130 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15183 = lookup_qname env lid  in
      match uu____15183 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15184,uu____15185,tps,uu____15187,uu____15188,uu____15189);
              FStar_Syntax_Syntax.sigrng = uu____15190;
              FStar_Syntax_Syntax.sigquals = uu____15191;
              FStar_Syntax_Syntax.sigmeta = uu____15192;
              FStar_Syntax_Syntax.sigattrs = uu____15193;_},uu____15194),uu____15195)
          -> FStar_List.length tps
      | uu____15258 ->
          let uu____15259 = name_not_found lid  in
          let uu____15264 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15259 uu____15264
  
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
           (fun uu____15308  ->
              match uu____15308 with
              | (d,uu____15316) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15331 = effect_decl_opt env l  in
      match uu____15331 with
      | FStar_Pervasives_Native.None  ->
          let uu____15346 = name_not_found l  in
          let uu____15351 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15346 uu____15351
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15373  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15392  ->
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
        let uu____15423 = FStar_Ident.lid_equals l1 l2  in
        if uu____15423
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15431 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15431
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15439 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15492  ->
                        match uu____15492 with
                        | (m1,m2,uu____15505,uu____15506,uu____15507) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15439 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15524 =
                    let uu____15529 =
                      let uu____15530 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15531 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15530
                        uu____15531
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15529)
                     in
                  FStar_Errors.raise_error uu____15524 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15538,uu____15539,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15572 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15572
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
  'Auu____15588 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15588)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15617 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15643  ->
                match uu____15643 with
                | (d,uu____15649) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15617 with
      | FStar_Pervasives_Native.None  ->
          let uu____15660 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15660
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15673 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15673 with
           | (uu____15688,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15704)::(wp,uu____15706)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15742 -> failwith "Impossible"))
  
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
          let uu____15795 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15795
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15797 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15797
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
                  let uu____15805 = get_range env  in
                  let uu____15806 =
                    let uu____15813 =
                      let uu____15814 =
                        let uu____15829 =
                          let uu____15838 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15838]  in
                        (null_wp, uu____15829)  in
                      FStar_Syntax_Syntax.Tm_app uu____15814  in
                    FStar_Syntax_Syntax.mk uu____15813  in
                  uu____15806 FStar_Pervasives_Native.None uu____15805  in
                let uu____15870 =
                  let uu____15871 =
                    let uu____15880 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15880]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15871;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15870))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___244_15911 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___244_15911.order);
              joins = (uu___244_15911.joins)
            }  in
          let uu___245_15920 = env  in
          {
            solver = (uu___245_15920.solver);
            range = (uu___245_15920.range);
            curmodule = (uu___245_15920.curmodule);
            gamma = (uu___245_15920.gamma);
            gamma_sig = (uu___245_15920.gamma_sig);
            gamma_cache = (uu___245_15920.gamma_cache);
            modules = (uu___245_15920.modules);
            expected_typ = (uu___245_15920.expected_typ);
            sigtab = (uu___245_15920.sigtab);
            is_pattern = (uu___245_15920.is_pattern);
            instantiate_imp = (uu___245_15920.instantiate_imp);
            effects;
            generalize = (uu___245_15920.generalize);
            letrecs = (uu___245_15920.letrecs);
            top_level = (uu___245_15920.top_level);
            check_uvars = (uu___245_15920.check_uvars);
            use_eq = (uu___245_15920.use_eq);
            is_iface = (uu___245_15920.is_iface);
            admit = (uu___245_15920.admit);
            lax = (uu___245_15920.lax);
            lax_universes = (uu___245_15920.lax_universes);
            phase1 = (uu___245_15920.phase1);
            failhard = (uu___245_15920.failhard);
            nosynth = (uu___245_15920.nosynth);
            uvar_subtyping = (uu___245_15920.uvar_subtyping);
            tc_term = (uu___245_15920.tc_term);
            type_of = (uu___245_15920.type_of);
            universe_of = (uu___245_15920.universe_of);
            check_type_of = (uu___245_15920.check_type_of);
            use_bv_sorts = (uu___245_15920.use_bv_sorts);
            qtbl_name_and_index = (uu___245_15920.qtbl_name_and_index);
            normalized_eff_names = (uu___245_15920.normalized_eff_names);
            proof_ns = (uu___245_15920.proof_ns);
            synth_hook = (uu___245_15920.synth_hook);
            splice = (uu___245_15920.splice);
            is_native_tactic = (uu___245_15920.is_native_tactic);
            identifier_info = (uu___245_15920.identifier_info);
            tc_hooks = (uu___245_15920.tc_hooks);
            dsenv = (uu___245_15920.dsenv);
            dep_graph = (uu___245_15920.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15950 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15950  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16108 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16109 = l1 u t wp e  in
                                l2 u t uu____16108 uu____16109))
                | uu____16110 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16182 = inst_tscheme_with lift_t [u]  in
            match uu____16182 with
            | (uu____16189,lift_t1) ->
                let uu____16191 =
                  let uu____16198 =
                    let uu____16199 =
                      let uu____16214 =
                        let uu____16223 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16230 =
                          let uu____16239 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16239]  in
                        uu____16223 :: uu____16230  in
                      (lift_t1, uu____16214)  in
                    FStar_Syntax_Syntax.Tm_app uu____16199  in
                  FStar_Syntax_Syntax.mk uu____16198  in
                uu____16191 FStar_Pervasives_Native.None
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
            let uu____16341 = inst_tscheme_with lift_t [u]  in
            match uu____16341 with
            | (uu____16348,lift_t1) ->
                let uu____16350 =
                  let uu____16357 =
                    let uu____16358 =
                      let uu____16373 =
                        let uu____16382 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16389 =
                          let uu____16398 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16405 =
                            let uu____16414 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16414]  in
                          uu____16398 :: uu____16405  in
                        uu____16382 :: uu____16389  in
                      (lift_t1, uu____16373)  in
                    FStar_Syntax_Syntax.Tm_app uu____16358  in
                  FStar_Syntax_Syntax.mk uu____16357  in
                uu____16350 FStar_Pervasives_Native.None
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
              let uu____16504 =
                let uu____16505 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16505
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16504  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16509 =
              let uu____16510 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16510  in
            let uu____16511 =
              let uu____16512 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16538 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16538)
                 in
              FStar_Util.dflt "none" uu____16512  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16509
              uu____16511
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16564  ->
                    match uu____16564 with
                    | (e,uu____16572) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16595 =
            match uu____16595 with
            | (i,j) ->
                let uu____16606 = FStar_Ident.lid_equals i j  in
                if uu____16606
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
              let uu____16638 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16648 = FStar_Ident.lid_equals i k  in
                        if uu____16648
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16659 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16659
                                  then []
                                  else
                                    (let uu____16663 =
                                       let uu____16672 =
                                         find_edge order1 (i, k)  in
                                       let uu____16675 =
                                         find_edge order1 (k, j)  in
                                       (uu____16672, uu____16675)  in
                                     match uu____16663 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16690 =
                                           compose_edges e1 e2  in
                                         [uu____16690]
                                     | uu____16691 -> [])))))
                 in
              FStar_List.append order1 uu____16638  in
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
                   let uu____16721 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16723 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16723
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16721
                   then
                     let uu____16728 =
                       let uu____16733 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16733)
                        in
                     let uu____16734 = get_range env  in
                     FStar_Errors.raise_error uu____16728 uu____16734
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16811 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16811
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16860 =
                                              let uu____16869 =
                                                find_edge order2 (i, k)  in
                                              let uu____16872 =
                                                find_edge order2 (j, k)  in
                                              (uu____16869, uu____16872)  in
                                            match uu____16860 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16914,uu____16915)
                                                     ->
                                                     let uu____16922 =
                                                       let uu____16927 =
                                                         let uu____16928 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16928
                                                          in
                                                       let uu____16931 =
                                                         let uu____16932 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16932
                                                          in
                                                       (uu____16927,
                                                         uu____16931)
                                                        in
                                                     (match uu____16922 with
                                                      | (true ,true ) ->
                                                          let uu____16943 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16943
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
                                            | uu____16968 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___246_17041 = env.effects  in
              { decls = (uu___246_17041.decls); order = order2; joins }  in
            let uu___247_17042 = env  in
            {
              solver = (uu___247_17042.solver);
              range = (uu___247_17042.range);
              curmodule = (uu___247_17042.curmodule);
              gamma = (uu___247_17042.gamma);
              gamma_sig = (uu___247_17042.gamma_sig);
              gamma_cache = (uu___247_17042.gamma_cache);
              modules = (uu___247_17042.modules);
              expected_typ = (uu___247_17042.expected_typ);
              sigtab = (uu___247_17042.sigtab);
              is_pattern = (uu___247_17042.is_pattern);
              instantiate_imp = (uu___247_17042.instantiate_imp);
              effects;
              generalize = (uu___247_17042.generalize);
              letrecs = (uu___247_17042.letrecs);
              top_level = (uu___247_17042.top_level);
              check_uvars = (uu___247_17042.check_uvars);
              use_eq = (uu___247_17042.use_eq);
              is_iface = (uu___247_17042.is_iface);
              admit = (uu___247_17042.admit);
              lax = (uu___247_17042.lax);
              lax_universes = (uu___247_17042.lax_universes);
              phase1 = (uu___247_17042.phase1);
              failhard = (uu___247_17042.failhard);
              nosynth = (uu___247_17042.nosynth);
              uvar_subtyping = (uu___247_17042.uvar_subtyping);
              tc_term = (uu___247_17042.tc_term);
              type_of = (uu___247_17042.type_of);
              universe_of = (uu___247_17042.universe_of);
              check_type_of = (uu___247_17042.check_type_of);
              use_bv_sorts = (uu___247_17042.use_bv_sorts);
              qtbl_name_and_index = (uu___247_17042.qtbl_name_and_index);
              normalized_eff_names = (uu___247_17042.normalized_eff_names);
              proof_ns = (uu___247_17042.proof_ns);
              synth_hook = (uu___247_17042.synth_hook);
              splice = (uu___247_17042.splice);
              is_native_tactic = (uu___247_17042.is_native_tactic);
              identifier_info = (uu___247_17042.identifier_info);
              tc_hooks = (uu___247_17042.tc_hooks);
              dsenv = (uu___247_17042.dsenv);
              dep_graph = (uu___247_17042.dep_graph)
            }))
      | uu____17043 -> env
  
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
        | uu____17071 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17083 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17083 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17100 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17100 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17118 =
                     let uu____17123 =
                       let uu____17124 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17129 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17136 =
                         let uu____17137 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17137  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17124 uu____17129 uu____17136
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17123)
                      in
                   FStar_Errors.raise_error uu____17118
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17142 =
                     let uu____17151 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17151 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17180  ->
                        fun uu____17181  ->
                          match (uu____17180, uu____17181) with
                          | ((x,uu____17203),(t,uu____17205)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17142
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____17224 =
                     let uu___248_17225 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___248_17225.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___248_17225.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___248_17225.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___248_17225.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____17224
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
          let uu____17255 = effect_decl_opt env effect_name  in
          match uu____17255 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17288 =
                only_reifiable &&
                  (let uu____17290 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17290)
                 in
              if uu____17288
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17306 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____17325 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____17354 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____17354
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____17355 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____17355
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____17367 =
                       let uu____17370 = get_range env  in
                       let uu____17371 =
                         let uu____17378 =
                           let uu____17379 =
                             let uu____17394 =
                               let uu____17403 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17403; wp]  in
                             (repr, uu____17394)  in
                           FStar_Syntax_Syntax.Tm_app uu____17379  in
                         FStar_Syntax_Syntax.mk uu____17378  in
                       uu____17371 FStar_Pervasives_Native.None uu____17370
                        in
                     FStar_Pervasives_Native.Some uu____17367)
  
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
          let uu____17483 =
            let uu____17488 =
              let uu____17489 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17489
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17488)  in
          let uu____17490 = get_range env  in
          FStar_Errors.raise_error uu____17483 uu____17490  in
        let uu____17491 = effect_repr_aux true env c u_c  in
        match uu____17491 with
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
      | uu____17537 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17548 =
        let uu____17549 = FStar_Syntax_Subst.compress t  in
        uu____17549.FStar_Syntax_Syntax.n  in
      match uu____17548 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17552,c) ->
          is_reifiable_comp env c
      | uu____17570 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___249_17591 = env  in
        {
          solver = (uu___249_17591.solver);
          range = (uu___249_17591.range);
          curmodule = (uu___249_17591.curmodule);
          gamma = (uu___249_17591.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___249_17591.gamma_cache);
          modules = (uu___249_17591.modules);
          expected_typ = (uu___249_17591.expected_typ);
          sigtab = (uu___249_17591.sigtab);
          is_pattern = (uu___249_17591.is_pattern);
          instantiate_imp = (uu___249_17591.instantiate_imp);
          effects = (uu___249_17591.effects);
          generalize = (uu___249_17591.generalize);
          letrecs = (uu___249_17591.letrecs);
          top_level = (uu___249_17591.top_level);
          check_uvars = (uu___249_17591.check_uvars);
          use_eq = (uu___249_17591.use_eq);
          is_iface = (uu___249_17591.is_iface);
          admit = (uu___249_17591.admit);
          lax = (uu___249_17591.lax);
          lax_universes = (uu___249_17591.lax_universes);
          phase1 = (uu___249_17591.phase1);
          failhard = (uu___249_17591.failhard);
          nosynth = (uu___249_17591.nosynth);
          uvar_subtyping = (uu___249_17591.uvar_subtyping);
          tc_term = (uu___249_17591.tc_term);
          type_of = (uu___249_17591.type_of);
          universe_of = (uu___249_17591.universe_of);
          check_type_of = (uu___249_17591.check_type_of);
          use_bv_sorts = (uu___249_17591.use_bv_sorts);
          qtbl_name_and_index = (uu___249_17591.qtbl_name_and_index);
          normalized_eff_names = (uu___249_17591.normalized_eff_names);
          proof_ns = (uu___249_17591.proof_ns);
          synth_hook = (uu___249_17591.synth_hook);
          splice = (uu___249_17591.splice);
          is_native_tactic = (uu___249_17591.is_native_tactic);
          identifier_info = (uu___249_17591.identifier_info);
          tc_hooks = (uu___249_17591.tc_hooks);
          dsenv = (uu___249_17591.dsenv);
          dep_graph = (uu___249_17591.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___250_17603 = env  in
      {
        solver = (uu___250_17603.solver);
        range = (uu___250_17603.range);
        curmodule = (uu___250_17603.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___250_17603.gamma_sig);
        gamma_cache = (uu___250_17603.gamma_cache);
        modules = (uu___250_17603.modules);
        expected_typ = (uu___250_17603.expected_typ);
        sigtab = (uu___250_17603.sigtab);
        is_pattern = (uu___250_17603.is_pattern);
        instantiate_imp = (uu___250_17603.instantiate_imp);
        effects = (uu___250_17603.effects);
        generalize = (uu___250_17603.generalize);
        letrecs = (uu___250_17603.letrecs);
        top_level = (uu___250_17603.top_level);
        check_uvars = (uu___250_17603.check_uvars);
        use_eq = (uu___250_17603.use_eq);
        is_iface = (uu___250_17603.is_iface);
        admit = (uu___250_17603.admit);
        lax = (uu___250_17603.lax);
        lax_universes = (uu___250_17603.lax_universes);
        phase1 = (uu___250_17603.phase1);
        failhard = (uu___250_17603.failhard);
        nosynth = (uu___250_17603.nosynth);
        uvar_subtyping = (uu___250_17603.uvar_subtyping);
        tc_term = (uu___250_17603.tc_term);
        type_of = (uu___250_17603.type_of);
        universe_of = (uu___250_17603.universe_of);
        check_type_of = (uu___250_17603.check_type_of);
        use_bv_sorts = (uu___250_17603.use_bv_sorts);
        qtbl_name_and_index = (uu___250_17603.qtbl_name_and_index);
        normalized_eff_names = (uu___250_17603.normalized_eff_names);
        proof_ns = (uu___250_17603.proof_ns);
        synth_hook = (uu___250_17603.synth_hook);
        splice = (uu___250_17603.splice);
        is_native_tactic = (uu___250_17603.is_native_tactic);
        identifier_info = (uu___250_17603.identifier_info);
        tc_hooks = (uu___250_17603.tc_hooks);
        dsenv = (uu___250_17603.dsenv);
        dep_graph = (uu___250_17603.dep_graph)
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
            (let uu___251_17658 = env  in
             {
               solver = (uu___251_17658.solver);
               range = (uu___251_17658.range);
               curmodule = (uu___251_17658.curmodule);
               gamma = rest;
               gamma_sig = (uu___251_17658.gamma_sig);
               gamma_cache = (uu___251_17658.gamma_cache);
               modules = (uu___251_17658.modules);
               expected_typ = (uu___251_17658.expected_typ);
               sigtab = (uu___251_17658.sigtab);
               is_pattern = (uu___251_17658.is_pattern);
               instantiate_imp = (uu___251_17658.instantiate_imp);
               effects = (uu___251_17658.effects);
               generalize = (uu___251_17658.generalize);
               letrecs = (uu___251_17658.letrecs);
               top_level = (uu___251_17658.top_level);
               check_uvars = (uu___251_17658.check_uvars);
               use_eq = (uu___251_17658.use_eq);
               is_iface = (uu___251_17658.is_iface);
               admit = (uu___251_17658.admit);
               lax = (uu___251_17658.lax);
               lax_universes = (uu___251_17658.lax_universes);
               phase1 = (uu___251_17658.phase1);
               failhard = (uu___251_17658.failhard);
               nosynth = (uu___251_17658.nosynth);
               uvar_subtyping = (uu___251_17658.uvar_subtyping);
               tc_term = (uu___251_17658.tc_term);
               type_of = (uu___251_17658.type_of);
               universe_of = (uu___251_17658.universe_of);
               check_type_of = (uu___251_17658.check_type_of);
               use_bv_sorts = (uu___251_17658.use_bv_sorts);
               qtbl_name_and_index = (uu___251_17658.qtbl_name_and_index);
               normalized_eff_names = (uu___251_17658.normalized_eff_names);
               proof_ns = (uu___251_17658.proof_ns);
               synth_hook = (uu___251_17658.synth_hook);
               splice = (uu___251_17658.splice);
               is_native_tactic = (uu___251_17658.is_native_tactic);
               identifier_info = (uu___251_17658.identifier_info);
               tc_hooks = (uu___251_17658.tc_hooks);
               dsenv = (uu___251_17658.dsenv);
               dep_graph = (uu___251_17658.dep_graph)
             }))
    | uu____17659 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17685  ->
             match uu____17685 with | (x,uu____17691) -> push_bv env1 x) env
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
            let uu___252_17721 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___252_17721.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___252_17721.FStar_Syntax_Syntax.index);
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
      (let uu___253_17761 = env  in
       {
         solver = (uu___253_17761.solver);
         range = (uu___253_17761.range);
         curmodule = (uu___253_17761.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___253_17761.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___253_17761.sigtab);
         is_pattern = (uu___253_17761.is_pattern);
         instantiate_imp = (uu___253_17761.instantiate_imp);
         effects = (uu___253_17761.effects);
         generalize = (uu___253_17761.generalize);
         letrecs = (uu___253_17761.letrecs);
         top_level = (uu___253_17761.top_level);
         check_uvars = (uu___253_17761.check_uvars);
         use_eq = (uu___253_17761.use_eq);
         is_iface = (uu___253_17761.is_iface);
         admit = (uu___253_17761.admit);
         lax = (uu___253_17761.lax);
         lax_universes = (uu___253_17761.lax_universes);
         phase1 = (uu___253_17761.phase1);
         failhard = (uu___253_17761.failhard);
         nosynth = (uu___253_17761.nosynth);
         uvar_subtyping = (uu___253_17761.uvar_subtyping);
         tc_term = (uu___253_17761.tc_term);
         type_of = (uu___253_17761.type_of);
         universe_of = (uu___253_17761.universe_of);
         check_type_of = (uu___253_17761.check_type_of);
         use_bv_sorts = (uu___253_17761.use_bv_sorts);
         qtbl_name_and_index = (uu___253_17761.qtbl_name_and_index);
         normalized_eff_names = (uu___253_17761.normalized_eff_names);
         proof_ns = (uu___253_17761.proof_ns);
         synth_hook = (uu___253_17761.synth_hook);
         splice = (uu___253_17761.splice);
         is_native_tactic = (uu___253_17761.is_native_tactic);
         identifier_info = (uu___253_17761.identifier_info);
         tc_hooks = (uu___253_17761.tc_hooks);
         dsenv = (uu___253_17761.dsenv);
         dep_graph = (uu___253_17761.dep_graph)
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
        let uu____17803 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17803 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17831 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17831)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___254_17846 = env  in
      {
        solver = (uu___254_17846.solver);
        range = (uu___254_17846.range);
        curmodule = (uu___254_17846.curmodule);
        gamma = (uu___254_17846.gamma);
        gamma_sig = (uu___254_17846.gamma_sig);
        gamma_cache = (uu___254_17846.gamma_cache);
        modules = (uu___254_17846.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___254_17846.sigtab);
        is_pattern = (uu___254_17846.is_pattern);
        instantiate_imp = (uu___254_17846.instantiate_imp);
        effects = (uu___254_17846.effects);
        generalize = (uu___254_17846.generalize);
        letrecs = (uu___254_17846.letrecs);
        top_level = (uu___254_17846.top_level);
        check_uvars = (uu___254_17846.check_uvars);
        use_eq = false;
        is_iface = (uu___254_17846.is_iface);
        admit = (uu___254_17846.admit);
        lax = (uu___254_17846.lax);
        lax_universes = (uu___254_17846.lax_universes);
        phase1 = (uu___254_17846.phase1);
        failhard = (uu___254_17846.failhard);
        nosynth = (uu___254_17846.nosynth);
        uvar_subtyping = (uu___254_17846.uvar_subtyping);
        tc_term = (uu___254_17846.tc_term);
        type_of = (uu___254_17846.type_of);
        universe_of = (uu___254_17846.universe_of);
        check_type_of = (uu___254_17846.check_type_of);
        use_bv_sorts = (uu___254_17846.use_bv_sorts);
        qtbl_name_and_index = (uu___254_17846.qtbl_name_and_index);
        normalized_eff_names = (uu___254_17846.normalized_eff_names);
        proof_ns = (uu___254_17846.proof_ns);
        synth_hook = (uu___254_17846.synth_hook);
        splice = (uu___254_17846.splice);
        is_native_tactic = (uu___254_17846.is_native_tactic);
        identifier_info = (uu___254_17846.identifier_info);
        tc_hooks = (uu___254_17846.tc_hooks);
        dsenv = (uu___254_17846.dsenv);
        dep_graph = (uu___254_17846.dep_graph)
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
    let uu____17874 = expected_typ env_  in
    ((let uu___255_17880 = env_  in
      {
        solver = (uu___255_17880.solver);
        range = (uu___255_17880.range);
        curmodule = (uu___255_17880.curmodule);
        gamma = (uu___255_17880.gamma);
        gamma_sig = (uu___255_17880.gamma_sig);
        gamma_cache = (uu___255_17880.gamma_cache);
        modules = (uu___255_17880.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___255_17880.sigtab);
        is_pattern = (uu___255_17880.is_pattern);
        instantiate_imp = (uu___255_17880.instantiate_imp);
        effects = (uu___255_17880.effects);
        generalize = (uu___255_17880.generalize);
        letrecs = (uu___255_17880.letrecs);
        top_level = (uu___255_17880.top_level);
        check_uvars = (uu___255_17880.check_uvars);
        use_eq = false;
        is_iface = (uu___255_17880.is_iface);
        admit = (uu___255_17880.admit);
        lax = (uu___255_17880.lax);
        lax_universes = (uu___255_17880.lax_universes);
        phase1 = (uu___255_17880.phase1);
        failhard = (uu___255_17880.failhard);
        nosynth = (uu___255_17880.nosynth);
        uvar_subtyping = (uu___255_17880.uvar_subtyping);
        tc_term = (uu___255_17880.tc_term);
        type_of = (uu___255_17880.type_of);
        universe_of = (uu___255_17880.universe_of);
        check_type_of = (uu___255_17880.check_type_of);
        use_bv_sorts = (uu___255_17880.use_bv_sorts);
        qtbl_name_and_index = (uu___255_17880.qtbl_name_and_index);
        normalized_eff_names = (uu___255_17880.normalized_eff_names);
        proof_ns = (uu___255_17880.proof_ns);
        synth_hook = (uu___255_17880.synth_hook);
        splice = (uu___255_17880.splice);
        is_native_tactic = (uu___255_17880.is_native_tactic);
        identifier_info = (uu___255_17880.identifier_info);
        tc_hooks = (uu___255_17880.tc_hooks);
        dsenv = (uu___255_17880.dsenv);
        dep_graph = (uu___255_17880.dep_graph)
      }), uu____17874)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17890 =
      let uu____17893 = FStar_Ident.id_of_text ""  in [uu____17893]  in
    FStar_Ident.lid_of_ids uu____17890  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17899 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17899
        then
          let uu____17902 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17902 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___256_17929 = env  in
       {
         solver = (uu___256_17929.solver);
         range = (uu___256_17929.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___256_17929.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___256_17929.expected_typ);
         sigtab = (uu___256_17929.sigtab);
         is_pattern = (uu___256_17929.is_pattern);
         instantiate_imp = (uu___256_17929.instantiate_imp);
         effects = (uu___256_17929.effects);
         generalize = (uu___256_17929.generalize);
         letrecs = (uu___256_17929.letrecs);
         top_level = (uu___256_17929.top_level);
         check_uvars = (uu___256_17929.check_uvars);
         use_eq = (uu___256_17929.use_eq);
         is_iface = (uu___256_17929.is_iface);
         admit = (uu___256_17929.admit);
         lax = (uu___256_17929.lax);
         lax_universes = (uu___256_17929.lax_universes);
         phase1 = (uu___256_17929.phase1);
         failhard = (uu___256_17929.failhard);
         nosynth = (uu___256_17929.nosynth);
         uvar_subtyping = (uu___256_17929.uvar_subtyping);
         tc_term = (uu___256_17929.tc_term);
         type_of = (uu___256_17929.type_of);
         universe_of = (uu___256_17929.universe_of);
         check_type_of = (uu___256_17929.check_type_of);
         use_bv_sorts = (uu___256_17929.use_bv_sorts);
         qtbl_name_and_index = (uu___256_17929.qtbl_name_and_index);
         normalized_eff_names = (uu___256_17929.normalized_eff_names);
         proof_ns = (uu___256_17929.proof_ns);
         synth_hook = (uu___256_17929.synth_hook);
         splice = (uu___256_17929.splice);
         is_native_tactic = (uu___256_17929.is_native_tactic);
         identifier_info = (uu___256_17929.identifier_info);
         tc_hooks = (uu___256_17929.tc_hooks);
         dsenv = (uu___256_17929.dsenv);
         dep_graph = (uu___256_17929.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17980)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17984,(uu____17985,t)))::tl1
          ->
          let uu____18006 =
            let uu____18009 = FStar_Syntax_Free.uvars t  in
            ext out uu____18009  in
          aux uu____18006 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18012;
            FStar_Syntax_Syntax.index = uu____18013;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18020 =
            let uu____18023 = FStar_Syntax_Free.uvars t  in
            ext out uu____18023  in
          aux uu____18020 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18080)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18084,(uu____18085,t)))::tl1
          ->
          let uu____18106 =
            let uu____18109 = FStar_Syntax_Free.univs t  in
            ext out uu____18109  in
          aux uu____18106 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18112;
            FStar_Syntax_Syntax.index = uu____18113;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18120 =
            let uu____18123 = FStar_Syntax_Free.univs t  in
            ext out uu____18123  in
          aux uu____18120 tl1
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
          let uu____18184 = FStar_Util.set_add uname out  in
          aux uu____18184 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18187,(uu____18188,t)))::tl1
          ->
          let uu____18209 =
            let uu____18212 = FStar_Syntax_Free.univnames t  in
            ext out uu____18212  in
          aux uu____18209 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18215;
            FStar_Syntax_Syntax.index = uu____18216;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18223 =
            let uu____18226 = FStar_Syntax_Free.univnames t  in
            ext out uu____18226  in
          aux uu____18223 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___230_18246  ->
            match uu___230_18246 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18250 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____18263 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____18273 =
      let uu____18280 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____18280
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____18273 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____18318 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___231_18328  ->
              match uu___231_18328 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____18330 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____18330
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____18333) ->
                  let uu____18350 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____18350))
       in
    FStar_All.pipe_right uu____18318 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___232_18357  ->
    match uu___232_18357 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____18359 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____18359
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18379  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18421) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18440,uu____18441) -> false  in
      let uu____18450 =
        FStar_List.tryFind
          (fun uu____18468  ->
             match uu____18468 with | (p,uu____18476) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18450 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18487,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18509 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18509
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___257_18527 = e  in
        {
          solver = (uu___257_18527.solver);
          range = (uu___257_18527.range);
          curmodule = (uu___257_18527.curmodule);
          gamma = (uu___257_18527.gamma);
          gamma_sig = (uu___257_18527.gamma_sig);
          gamma_cache = (uu___257_18527.gamma_cache);
          modules = (uu___257_18527.modules);
          expected_typ = (uu___257_18527.expected_typ);
          sigtab = (uu___257_18527.sigtab);
          is_pattern = (uu___257_18527.is_pattern);
          instantiate_imp = (uu___257_18527.instantiate_imp);
          effects = (uu___257_18527.effects);
          generalize = (uu___257_18527.generalize);
          letrecs = (uu___257_18527.letrecs);
          top_level = (uu___257_18527.top_level);
          check_uvars = (uu___257_18527.check_uvars);
          use_eq = (uu___257_18527.use_eq);
          is_iface = (uu___257_18527.is_iface);
          admit = (uu___257_18527.admit);
          lax = (uu___257_18527.lax);
          lax_universes = (uu___257_18527.lax_universes);
          phase1 = (uu___257_18527.phase1);
          failhard = (uu___257_18527.failhard);
          nosynth = (uu___257_18527.nosynth);
          uvar_subtyping = (uu___257_18527.uvar_subtyping);
          tc_term = (uu___257_18527.tc_term);
          type_of = (uu___257_18527.type_of);
          universe_of = (uu___257_18527.universe_of);
          check_type_of = (uu___257_18527.check_type_of);
          use_bv_sorts = (uu___257_18527.use_bv_sorts);
          qtbl_name_and_index = (uu___257_18527.qtbl_name_and_index);
          normalized_eff_names = (uu___257_18527.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___257_18527.synth_hook);
          splice = (uu___257_18527.splice);
          is_native_tactic = (uu___257_18527.is_native_tactic);
          identifier_info = (uu___257_18527.identifier_info);
          tc_hooks = (uu___257_18527.tc_hooks);
          dsenv = (uu___257_18527.dsenv);
          dep_graph = (uu___257_18527.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___258_18567 = e  in
      {
        solver = (uu___258_18567.solver);
        range = (uu___258_18567.range);
        curmodule = (uu___258_18567.curmodule);
        gamma = (uu___258_18567.gamma);
        gamma_sig = (uu___258_18567.gamma_sig);
        gamma_cache = (uu___258_18567.gamma_cache);
        modules = (uu___258_18567.modules);
        expected_typ = (uu___258_18567.expected_typ);
        sigtab = (uu___258_18567.sigtab);
        is_pattern = (uu___258_18567.is_pattern);
        instantiate_imp = (uu___258_18567.instantiate_imp);
        effects = (uu___258_18567.effects);
        generalize = (uu___258_18567.generalize);
        letrecs = (uu___258_18567.letrecs);
        top_level = (uu___258_18567.top_level);
        check_uvars = (uu___258_18567.check_uvars);
        use_eq = (uu___258_18567.use_eq);
        is_iface = (uu___258_18567.is_iface);
        admit = (uu___258_18567.admit);
        lax = (uu___258_18567.lax);
        lax_universes = (uu___258_18567.lax_universes);
        phase1 = (uu___258_18567.phase1);
        failhard = (uu___258_18567.failhard);
        nosynth = (uu___258_18567.nosynth);
        uvar_subtyping = (uu___258_18567.uvar_subtyping);
        tc_term = (uu___258_18567.tc_term);
        type_of = (uu___258_18567.type_of);
        universe_of = (uu___258_18567.universe_of);
        check_type_of = (uu___258_18567.check_type_of);
        use_bv_sorts = (uu___258_18567.use_bv_sorts);
        qtbl_name_and_index = (uu___258_18567.qtbl_name_and_index);
        normalized_eff_names = (uu___258_18567.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___258_18567.synth_hook);
        splice = (uu___258_18567.splice);
        is_native_tactic = (uu___258_18567.is_native_tactic);
        identifier_info = (uu___258_18567.identifier_info);
        tc_hooks = (uu___258_18567.tc_hooks);
        dsenv = (uu___258_18567.dsenv);
        dep_graph = (uu___258_18567.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18582 = FStar_Syntax_Free.names t  in
      let uu____18585 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18582 uu____18585
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18606 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18606
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18614 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18614
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18631 =
      match uu____18631 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18641 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18641)
       in
    let uu____18643 =
      let uu____18646 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18646 FStar_List.rev  in
    FStar_All.pipe_right uu____18643 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = [];
        univ_ineqs = ([],[]); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun uu____18732  ->
                match uu____18732 with
                | (uu____18741,uu____18742,ctx_uvar,uu____18744) ->
                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check =
                       FStar_Syntax_Syntax.Allow_unresolved)
                      ||
                      (let uu____18747 =
                         FStar_Syntax_Unionfind.find
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       (match uu____18747 with
                        | FStar_Pervasives_Native.Some uu____18750 -> true
                        | FStar_Pervasives_Native.None  -> false))))
    | uu____18751 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____18757;
        univ_ineqs = uu____18758; implicits = uu____18759;_} -> true
    | uu____18778 -> false
  
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___259_18813 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___259_18813.deferred);
            univ_ineqs = (uu___259_18813.univ_ineqs);
            implicits = (uu___259_18813.implicits)
          }
  
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____18848 = FStar_Options.defensive ()  in
          if uu____18848
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____18852 =
              let uu____18853 =
                let uu____18854 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____18854  in
              Prims.op_Negation uu____18853  in
            (if uu____18852
             then
               let uu____18859 =
                 let uu____18864 =
                   let uu____18865 = FStar_Syntax_Print.term_to_string t  in
                   let uu____18866 =
                     let uu____18867 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____18867
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____18865 uu____18866
                    in
                 (FStar_Errors.Warning_Defensive, uu____18864)  in
               FStar_Errors.log_issue rng uu____18859
             else ())
          else ()
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____18898 =
            let uu____18899 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____18899  in
          if uu____18898
          then ()
          else
            (let uu____18901 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____18901 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____18924 =
            let uu____18925 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____18925  in
          if uu____18924
          then ()
          else
            (let uu____18927 = bound_vars e  in
             def_check_closed_in rng msg uu____18927 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___260_18962 = g  in
          let uu____18963 =
            let uu____18964 =
              let uu____18965 =
                let uu____18972 =
                  let uu____18973 =
                    let uu____18988 =
                      let uu____18997 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____18997]  in
                    (f, uu____18988)  in
                  FStar_Syntax_Syntax.Tm_app uu____18973  in
                FStar_Syntax_Syntax.mk uu____18972  in
              uu____18965 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____18964
             in
          {
            guard_f = uu____18963;
            deferred = (uu___260_18962.deferred);
            univ_ineqs = (uu___260_18962.univ_ineqs);
            implicits = (uu___260_18962.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___261_19045 = g  in
          let uu____19046 =
            let uu____19047 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19047  in
          {
            guard_f = uu____19046;
            deferred = (uu___261_19045.deferred);
            univ_ineqs = (uu___261_19045.univ_ineqs);
            implicits = (uu___261_19045.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19053 ->
        failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____19068 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19068
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19074 =
      let uu____19075 = FStar_Syntax_Util.unmeta t  in
      uu____19075.FStar_Syntax_Syntax.n  in
    match uu____19074 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19079 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____19120 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19120;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____19205 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____19205
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___262_19207 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___262_19207.deferred);
              univ_ineqs = (uu___262_19207.univ_ineqs);
              implicits = (uu___262_19207.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____19236 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____19236
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___263_19255 = g  in
            let uu____19256 =
              let uu____19257 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____19257  in
            {
              guard_f = uu____19256;
              deferred = (uu___263_19255.deferred);
              univ_ineqs = (uu___263_19255.univ_ineqs);
              implicits = (uu___263_19255.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,guard_t)
              FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            let uu____19295 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____19295 with
            | FStar_Pervasives_Native.Some
                (uu____19318::(tm,uu____19320)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____19370 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____19386 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____19386;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                   true gamma binders;
                 (let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_uvar
                         (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                      FStar_Pervasives_Native.None r
                     in
                  let g =
                    let uu___264_19416 = trivial_guard  in
                    {
                      guard_f = (uu___264_19416.guard_f);
                      deferred = (uu___264_19416.deferred);
                      univ_ineqs = (uu___264_19416.univ_ineqs);
                      implicits = [(reason, t, ctx_uvar, r)]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____19449  -> ());
    push = (fun uu____19451  -> ());
    pop = (fun uu____19453  -> ());
    snapshot =
      (fun uu____19455  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____19464  -> fun uu____19465  -> ());
    encode_modul = (fun uu____19476  -> fun uu____19477  -> ());
    encode_sig = (fun uu____19480  -> fun uu____19481  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____19487 =
             let uu____19494 = FStar_Options.peek ()  in (e, g, uu____19494)
              in
           [uu____19487]);
    solve = (fun uu____19510  -> fun uu____19511  -> fun uu____19512  -> ());
    finish = (fun uu____19518  -> ());
    refresh = (fun uu____19520  -> ())
  } 