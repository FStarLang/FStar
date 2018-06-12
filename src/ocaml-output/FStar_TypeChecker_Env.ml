open Prims
type sig_binding =
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
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
           (fun uu___219_8452  ->
              match uu___219_8452 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8455 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8455  in
                  let uu____8456 =
                    let uu____8457 = FStar_Syntax_Subst.compress y  in
                    uu____8457.FStar_Syntax_Syntax.n  in
                  (match uu____8456 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8461 =
                         let uu___233_8462 = y1  in
                         let uu____8463 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___233_8462.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___233_8462.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8463
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8461
                   | uu____8466 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___234_8478 = env  in
      let uu____8479 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___234_8478.solver);
        range = (uu___234_8478.range);
        curmodule = (uu___234_8478.curmodule);
        gamma = uu____8479;
        gamma_sig = (uu___234_8478.gamma_sig);
        gamma_cache = (uu___234_8478.gamma_cache);
        modules = (uu___234_8478.modules);
        expected_typ = (uu___234_8478.expected_typ);
        sigtab = (uu___234_8478.sigtab);
        is_pattern = (uu___234_8478.is_pattern);
        instantiate_imp = (uu___234_8478.instantiate_imp);
        effects = (uu___234_8478.effects);
        generalize = (uu___234_8478.generalize);
        letrecs = (uu___234_8478.letrecs);
        top_level = (uu___234_8478.top_level);
        check_uvars = (uu___234_8478.check_uvars);
        use_eq = (uu___234_8478.use_eq);
        is_iface = (uu___234_8478.is_iface);
        admit = (uu___234_8478.admit);
        lax = (uu___234_8478.lax);
        lax_universes = (uu___234_8478.lax_universes);
        phase1 = (uu___234_8478.phase1);
        failhard = (uu___234_8478.failhard);
        nosynth = (uu___234_8478.nosynth);
        uvar_subtyping = (uu___234_8478.uvar_subtyping);
        tc_term = (uu___234_8478.tc_term);
        type_of = (uu___234_8478.type_of);
        universe_of = (uu___234_8478.universe_of);
        check_type_of = (uu___234_8478.check_type_of);
        use_bv_sorts = (uu___234_8478.use_bv_sorts);
        qtbl_name_and_index = (uu___234_8478.qtbl_name_and_index);
        normalized_eff_names = (uu___234_8478.normalized_eff_names);
        proof_ns = (uu___234_8478.proof_ns);
        synth_hook = (uu___234_8478.synth_hook);
        splice = (uu___234_8478.splice);
        is_native_tactic = (uu___234_8478.is_native_tactic);
        identifier_info = (uu___234_8478.identifier_info);
        tc_hooks = (uu___234_8478.tc_hooks);
        dsenv = (uu___234_8478.dsenv);
        dep_graph = (uu___234_8478.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8486  -> fun uu____8487  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___235_8507 = env  in
      {
        solver = (uu___235_8507.solver);
        range = (uu___235_8507.range);
        curmodule = (uu___235_8507.curmodule);
        gamma = (uu___235_8507.gamma);
        gamma_sig = (uu___235_8507.gamma_sig);
        gamma_cache = (uu___235_8507.gamma_cache);
        modules = (uu___235_8507.modules);
        expected_typ = (uu___235_8507.expected_typ);
        sigtab = (uu___235_8507.sigtab);
        is_pattern = (uu___235_8507.is_pattern);
        instantiate_imp = (uu___235_8507.instantiate_imp);
        effects = (uu___235_8507.effects);
        generalize = (uu___235_8507.generalize);
        letrecs = (uu___235_8507.letrecs);
        top_level = (uu___235_8507.top_level);
        check_uvars = (uu___235_8507.check_uvars);
        use_eq = (uu___235_8507.use_eq);
        is_iface = (uu___235_8507.is_iface);
        admit = (uu___235_8507.admit);
        lax = (uu___235_8507.lax);
        lax_universes = (uu___235_8507.lax_universes);
        phase1 = (uu___235_8507.phase1);
        failhard = (uu___235_8507.failhard);
        nosynth = (uu___235_8507.nosynth);
        uvar_subtyping = (uu___235_8507.uvar_subtyping);
        tc_term = (uu___235_8507.tc_term);
        type_of = (uu___235_8507.type_of);
        universe_of = (uu___235_8507.universe_of);
        check_type_of = (uu___235_8507.check_type_of);
        use_bv_sorts = (uu___235_8507.use_bv_sorts);
        qtbl_name_and_index = (uu___235_8507.qtbl_name_and_index);
        normalized_eff_names = (uu___235_8507.normalized_eff_names);
        proof_ns = (uu___235_8507.proof_ns);
        synth_hook = (uu___235_8507.synth_hook);
        splice = (uu___235_8507.splice);
        is_native_tactic = (uu___235_8507.is_native_tactic);
        identifier_info = (uu___235_8507.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___235_8507.dsenv);
        dep_graph = (uu___235_8507.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___236_8518 = e  in
      {
        solver = (uu___236_8518.solver);
        range = (uu___236_8518.range);
        curmodule = (uu___236_8518.curmodule);
        gamma = (uu___236_8518.gamma);
        gamma_sig = (uu___236_8518.gamma_sig);
        gamma_cache = (uu___236_8518.gamma_cache);
        modules = (uu___236_8518.modules);
        expected_typ = (uu___236_8518.expected_typ);
        sigtab = (uu___236_8518.sigtab);
        is_pattern = (uu___236_8518.is_pattern);
        instantiate_imp = (uu___236_8518.instantiate_imp);
        effects = (uu___236_8518.effects);
        generalize = (uu___236_8518.generalize);
        letrecs = (uu___236_8518.letrecs);
        top_level = (uu___236_8518.top_level);
        check_uvars = (uu___236_8518.check_uvars);
        use_eq = (uu___236_8518.use_eq);
        is_iface = (uu___236_8518.is_iface);
        admit = (uu___236_8518.admit);
        lax = (uu___236_8518.lax);
        lax_universes = (uu___236_8518.lax_universes);
        phase1 = (uu___236_8518.phase1);
        failhard = (uu___236_8518.failhard);
        nosynth = (uu___236_8518.nosynth);
        uvar_subtyping = (uu___236_8518.uvar_subtyping);
        tc_term = (uu___236_8518.tc_term);
        type_of = (uu___236_8518.type_of);
        universe_of = (uu___236_8518.universe_of);
        check_type_of = (uu___236_8518.check_type_of);
        use_bv_sorts = (uu___236_8518.use_bv_sorts);
        qtbl_name_and_index = (uu___236_8518.qtbl_name_and_index);
        normalized_eff_names = (uu___236_8518.normalized_eff_names);
        proof_ns = (uu___236_8518.proof_ns);
        synth_hook = (uu___236_8518.synth_hook);
        splice = (uu___236_8518.splice);
        is_native_tactic = (uu___236_8518.is_native_tactic);
        identifier_info = (uu___236_8518.identifier_info);
        tc_hooks = (uu___236_8518.tc_hooks);
        dsenv = (uu___236_8518.dsenv);
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
      | (NoDelta ,uu____8541) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8542,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8543,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8544 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8553 . unit -> 'Auu____8553 FStar_Util.smap =
  fun uu____8560  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8565 . unit -> 'Auu____8565 FStar_Util.smap =
  fun uu____8572  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8682 = new_gamma_cache ()  in
                let uu____8685 = new_sigtab ()  in
                let uu____8688 =
                  let uu____8701 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8701, FStar_Pervasives_Native.None)  in
                let uu____8716 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8719 = FStar_Options.using_facts_from ()  in
                let uu____8720 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8723 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____8682;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8685;
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
                  qtbl_name_and_index = uu____8688;
                  normalized_eff_names = uu____8716;
                  proof_ns = uu____8719;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8759  -> false);
                  identifier_info = uu____8720;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8723;
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
  fun uu____8850  ->
    let uu____8851 = FStar_ST.op_Bang query_indices  in
    match uu____8851 with
    | [] -> failwith "Empty query indices!"
    | uu____8905 ->
        let uu____8914 =
          let uu____8923 =
            let uu____8930 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8930  in
          let uu____8984 = FStar_ST.op_Bang query_indices  in uu____8923 ::
            uu____8984
           in
        FStar_ST.op_Colon_Equals query_indices uu____8914
  
let (pop_query_indices : unit -> unit) =
  fun uu____9081  ->
    let uu____9082 = FStar_ST.op_Bang query_indices  in
    match uu____9082 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9205  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9235  ->
    match uu____9235 with
    | (l,n1) ->
        let uu____9242 = FStar_ST.op_Bang query_indices  in
        (match uu____9242 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9361 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9380  ->
    let uu____9381 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9381
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9458 =
       let uu____9461 = FStar_ST.op_Bang stack  in env :: uu____9461  in
     FStar_ST.op_Colon_Equals stack uu____9458);
    (let uu___237_9518 = env  in
     let uu____9519 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9522 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9525 =
       let uu____9538 =
         let uu____9541 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9541  in
       let uu____9566 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9538, uu____9566)  in
     let uu____9607 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9610 =
       let uu____9613 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9613  in
     {
       solver = (uu___237_9518.solver);
       range = (uu___237_9518.range);
       curmodule = (uu___237_9518.curmodule);
       gamma = (uu___237_9518.gamma);
       gamma_sig = (uu___237_9518.gamma_sig);
       gamma_cache = uu____9519;
       modules = (uu___237_9518.modules);
       expected_typ = (uu___237_9518.expected_typ);
       sigtab = uu____9522;
       is_pattern = (uu___237_9518.is_pattern);
       instantiate_imp = (uu___237_9518.instantiate_imp);
       effects = (uu___237_9518.effects);
       generalize = (uu___237_9518.generalize);
       letrecs = (uu___237_9518.letrecs);
       top_level = (uu___237_9518.top_level);
       check_uvars = (uu___237_9518.check_uvars);
       use_eq = (uu___237_9518.use_eq);
       is_iface = (uu___237_9518.is_iface);
       admit = (uu___237_9518.admit);
       lax = (uu___237_9518.lax);
       lax_universes = (uu___237_9518.lax_universes);
       phase1 = (uu___237_9518.phase1);
       failhard = (uu___237_9518.failhard);
       nosynth = (uu___237_9518.nosynth);
       uvar_subtyping = (uu___237_9518.uvar_subtyping);
       tc_term = (uu___237_9518.tc_term);
       type_of = (uu___237_9518.type_of);
       universe_of = (uu___237_9518.universe_of);
       check_type_of = (uu___237_9518.check_type_of);
       use_bv_sorts = (uu___237_9518.use_bv_sorts);
       qtbl_name_and_index = uu____9525;
       normalized_eff_names = uu____9607;
       proof_ns = (uu___237_9518.proof_ns);
       synth_hook = (uu___237_9518.synth_hook);
       splice = (uu___237_9518.splice);
       is_native_tactic = (uu___237_9518.is_native_tactic);
       identifier_info = uu____9610;
       tc_hooks = (uu___237_9518.tc_hooks);
       dsenv = (uu___237_9518.dsenv);
       dep_graph = (uu___237_9518.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9663  ->
    let uu____9664 = FStar_ST.op_Bang stack  in
    match uu____9664 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9726 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____9798  ->
           let uu____9799 = snapshot_stack env  in
           match uu____9799 with
           | (stack_depth,env1) ->
               let uu____9824 = snapshot_query_indices ()  in
               (match uu____9824 with
                | (query_indices_depth,()) ->
                    let uu____9848 = (env1.solver).snapshot msg  in
                    (match uu____9848 with
                     | (solver_depth,()) ->
                         let uu____9890 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9890 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___238_9936 = env1  in
                                 {
                                   solver = (uu___238_9936.solver);
                                   range = (uu___238_9936.range);
                                   curmodule = (uu___238_9936.curmodule);
                                   gamma = (uu___238_9936.gamma);
                                   gamma_sig = (uu___238_9936.gamma_sig);
                                   gamma_cache = (uu___238_9936.gamma_cache);
                                   modules = (uu___238_9936.modules);
                                   expected_typ =
                                     (uu___238_9936.expected_typ);
                                   sigtab = (uu___238_9936.sigtab);
                                   is_pattern = (uu___238_9936.is_pattern);
                                   instantiate_imp =
                                     (uu___238_9936.instantiate_imp);
                                   effects = (uu___238_9936.effects);
                                   generalize = (uu___238_9936.generalize);
                                   letrecs = (uu___238_9936.letrecs);
                                   top_level = (uu___238_9936.top_level);
                                   check_uvars = (uu___238_9936.check_uvars);
                                   use_eq = (uu___238_9936.use_eq);
                                   is_iface = (uu___238_9936.is_iface);
                                   admit = (uu___238_9936.admit);
                                   lax = (uu___238_9936.lax);
                                   lax_universes =
                                     (uu___238_9936.lax_universes);
                                   phase1 = (uu___238_9936.phase1);
                                   failhard = (uu___238_9936.failhard);
                                   nosynth = (uu___238_9936.nosynth);
                                   uvar_subtyping =
                                     (uu___238_9936.uvar_subtyping);
                                   tc_term = (uu___238_9936.tc_term);
                                   type_of = (uu___238_9936.type_of);
                                   universe_of = (uu___238_9936.universe_of);
                                   check_type_of =
                                     (uu___238_9936.check_type_of);
                                   use_bv_sorts =
                                     (uu___238_9936.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___238_9936.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___238_9936.normalized_eff_names);
                                   proof_ns = (uu___238_9936.proof_ns);
                                   synth_hook = (uu___238_9936.synth_hook);
                                   splice = (uu___238_9936.splice);
                                   is_native_tactic =
                                     (uu___238_9936.is_native_tactic);
                                   identifier_info =
                                     (uu___238_9936.identifier_info);
                                   tc_hooks = (uu___238_9936.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___238_9936.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9967  ->
             let uu____9968 =
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
             match uu____9968 with
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
                             ((let uu____10094 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____10094
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____10105 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____10105
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____10132,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____10164 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10190  ->
                  match uu____10190 with
                  | (m,uu____10196) -> FStar_Ident.lid_equals l m))
           in
        (match uu____10164 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___239_10204 = env  in
               {
                 solver = (uu___239_10204.solver);
                 range = (uu___239_10204.range);
                 curmodule = (uu___239_10204.curmodule);
                 gamma = (uu___239_10204.gamma);
                 gamma_sig = (uu___239_10204.gamma_sig);
                 gamma_cache = (uu___239_10204.gamma_cache);
                 modules = (uu___239_10204.modules);
                 expected_typ = (uu___239_10204.expected_typ);
                 sigtab = (uu___239_10204.sigtab);
                 is_pattern = (uu___239_10204.is_pattern);
                 instantiate_imp = (uu___239_10204.instantiate_imp);
                 effects = (uu___239_10204.effects);
                 generalize = (uu___239_10204.generalize);
                 letrecs = (uu___239_10204.letrecs);
                 top_level = (uu___239_10204.top_level);
                 check_uvars = (uu___239_10204.check_uvars);
                 use_eq = (uu___239_10204.use_eq);
                 is_iface = (uu___239_10204.is_iface);
                 admit = (uu___239_10204.admit);
                 lax = (uu___239_10204.lax);
                 lax_universes = (uu___239_10204.lax_universes);
                 phase1 = (uu___239_10204.phase1);
                 failhard = (uu___239_10204.failhard);
                 nosynth = (uu___239_10204.nosynth);
                 uvar_subtyping = (uu___239_10204.uvar_subtyping);
                 tc_term = (uu___239_10204.tc_term);
                 type_of = (uu___239_10204.type_of);
                 universe_of = (uu___239_10204.universe_of);
                 check_type_of = (uu___239_10204.check_type_of);
                 use_bv_sorts = (uu___239_10204.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___239_10204.normalized_eff_names);
                 proof_ns = (uu___239_10204.proof_ns);
                 synth_hook = (uu___239_10204.synth_hook);
                 splice = (uu___239_10204.splice);
                 is_native_tactic = (uu___239_10204.is_native_tactic);
                 identifier_info = (uu___239_10204.identifier_info);
                 tc_hooks = (uu___239_10204.tc_hooks);
                 dsenv = (uu___239_10204.dsenv);
                 dep_graph = (uu___239_10204.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____10217,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_10226 = env  in
               {
                 solver = (uu___240_10226.solver);
                 range = (uu___240_10226.range);
                 curmodule = (uu___240_10226.curmodule);
                 gamma = (uu___240_10226.gamma);
                 gamma_sig = (uu___240_10226.gamma_sig);
                 gamma_cache = (uu___240_10226.gamma_cache);
                 modules = (uu___240_10226.modules);
                 expected_typ = (uu___240_10226.expected_typ);
                 sigtab = (uu___240_10226.sigtab);
                 is_pattern = (uu___240_10226.is_pattern);
                 instantiate_imp = (uu___240_10226.instantiate_imp);
                 effects = (uu___240_10226.effects);
                 generalize = (uu___240_10226.generalize);
                 letrecs = (uu___240_10226.letrecs);
                 top_level = (uu___240_10226.top_level);
                 check_uvars = (uu___240_10226.check_uvars);
                 use_eq = (uu___240_10226.use_eq);
                 is_iface = (uu___240_10226.is_iface);
                 admit = (uu___240_10226.admit);
                 lax = (uu___240_10226.lax);
                 lax_universes = (uu___240_10226.lax_universes);
                 phase1 = (uu___240_10226.phase1);
                 failhard = (uu___240_10226.failhard);
                 nosynth = (uu___240_10226.nosynth);
                 uvar_subtyping = (uu___240_10226.uvar_subtyping);
                 tc_term = (uu___240_10226.tc_term);
                 type_of = (uu___240_10226.type_of);
                 universe_of = (uu___240_10226.universe_of);
                 check_type_of = (uu___240_10226.check_type_of);
                 use_bv_sorts = (uu___240_10226.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_10226.normalized_eff_names);
                 proof_ns = (uu___240_10226.proof_ns);
                 synth_hook = (uu___240_10226.synth_hook);
                 splice = (uu___240_10226.splice);
                 is_native_tactic = (uu___240_10226.is_native_tactic);
                 identifier_info = (uu___240_10226.identifier_info);
                 tc_hooks = (uu___240_10226.tc_hooks);
                 dsenv = (uu___240_10226.dsenv);
                 dep_graph = (uu___240_10226.dep_graph)
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
        (let uu___241_10260 = e  in
         {
           solver = (uu___241_10260.solver);
           range = r;
           curmodule = (uu___241_10260.curmodule);
           gamma = (uu___241_10260.gamma);
           gamma_sig = (uu___241_10260.gamma_sig);
           gamma_cache = (uu___241_10260.gamma_cache);
           modules = (uu___241_10260.modules);
           expected_typ = (uu___241_10260.expected_typ);
           sigtab = (uu___241_10260.sigtab);
           is_pattern = (uu___241_10260.is_pattern);
           instantiate_imp = (uu___241_10260.instantiate_imp);
           effects = (uu___241_10260.effects);
           generalize = (uu___241_10260.generalize);
           letrecs = (uu___241_10260.letrecs);
           top_level = (uu___241_10260.top_level);
           check_uvars = (uu___241_10260.check_uvars);
           use_eq = (uu___241_10260.use_eq);
           is_iface = (uu___241_10260.is_iface);
           admit = (uu___241_10260.admit);
           lax = (uu___241_10260.lax);
           lax_universes = (uu___241_10260.lax_universes);
           phase1 = (uu___241_10260.phase1);
           failhard = (uu___241_10260.failhard);
           nosynth = (uu___241_10260.nosynth);
           uvar_subtyping = (uu___241_10260.uvar_subtyping);
           tc_term = (uu___241_10260.tc_term);
           type_of = (uu___241_10260.type_of);
           universe_of = (uu___241_10260.universe_of);
           check_type_of = (uu___241_10260.check_type_of);
           use_bv_sorts = (uu___241_10260.use_bv_sorts);
           qtbl_name_and_index = (uu___241_10260.qtbl_name_and_index);
           normalized_eff_names = (uu___241_10260.normalized_eff_names);
           proof_ns = (uu___241_10260.proof_ns);
           synth_hook = (uu___241_10260.synth_hook);
           splice = (uu___241_10260.splice);
           is_native_tactic = (uu___241_10260.is_native_tactic);
           identifier_info = (uu___241_10260.identifier_info);
           tc_hooks = (uu___241_10260.tc_hooks);
           dsenv = (uu___241_10260.dsenv);
           dep_graph = (uu___241_10260.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10276 =
        let uu____10277 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10277 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10276
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10339 =
          let uu____10340 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10340 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10339
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10402 =
          let uu____10403 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10403 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10402
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10465 =
        let uu____10466 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10466 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10465
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___242_10535 = env  in
      {
        solver = (uu___242_10535.solver);
        range = (uu___242_10535.range);
        curmodule = lid;
        gamma = (uu___242_10535.gamma);
        gamma_sig = (uu___242_10535.gamma_sig);
        gamma_cache = (uu___242_10535.gamma_cache);
        modules = (uu___242_10535.modules);
        expected_typ = (uu___242_10535.expected_typ);
        sigtab = (uu___242_10535.sigtab);
        is_pattern = (uu___242_10535.is_pattern);
        instantiate_imp = (uu___242_10535.instantiate_imp);
        effects = (uu___242_10535.effects);
        generalize = (uu___242_10535.generalize);
        letrecs = (uu___242_10535.letrecs);
        top_level = (uu___242_10535.top_level);
        check_uvars = (uu___242_10535.check_uvars);
        use_eq = (uu___242_10535.use_eq);
        is_iface = (uu___242_10535.is_iface);
        admit = (uu___242_10535.admit);
        lax = (uu___242_10535.lax);
        lax_universes = (uu___242_10535.lax_universes);
        phase1 = (uu___242_10535.phase1);
        failhard = (uu___242_10535.failhard);
        nosynth = (uu___242_10535.nosynth);
        uvar_subtyping = (uu___242_10535.uvar_subtyping);
        tc_term = (uu___242_10535.tc_term);
        type_of = (uu___242_10535.type_of);
        universe_of = (uu___242_10535.universe_of);
        check_type_of = (uu___242_10535.check_type_of);
        use_bv_sorts = (uu___242_10535.use_bv_sorts);
        qtbl_name_and_index = (uu___242_10535.qtbl_name_and_index);
        normalized_eff_names = (uu___242_10535.normalized_eff_names);
        proof_ns = (uu___242_10535.proof_ns);
        synth_hook = (uu___242_10535.synth_hook);
        splice = (uu___242_10535.splice);
        is_native_tactic = (uu___242_10535.is_native_tactic);
        identifier_info = (uu___242_10535.identifier_info);
        tc_hooks = (uu___242_10535.tc_hooks);
        dsenv = (uu___242_10535.dsenv);
        dep_graph = (uu___242_10535.dep_graph)
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
      let uu____10562 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10562
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10572 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10572)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10582 =
      let uu____10583 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10583  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10582)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10588  ->
    let uu____10589 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10589
  
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
      | ((formals,t),uu____10645) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10679 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10679)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___220_10695  ->
    match uu___220_10695 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10721  -> new_u_univ ()))
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
      let uu____10740 = inst_tscheme t  in
      match uu____10740 with
      | (us,t1) ->
          let uu____10751 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10751)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10771  ->
          match uu____10771 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10790 =
                         let uu____10791 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10792 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10793 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10794 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10791 uu____10792 uu____10793 uu____10794
                          in
                       failwith uu____10790)
                    else ();
                    (let uu____10796 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10796))
               | uu____10805 ->
                   let uu____10806 =
                     let uu____10807 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10807
                      in
                   failwith uu____10806)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10813 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10819 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10825 -> false
  
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
             | ([],uu____10867) -> Maybe
             | (uu____10874,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10893 -> No  in
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
          let uu____10984 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10984 with
          | FStar_Pervasives_Native.None  ->
              let uu____11007 =
                FStar_Util.find_map env.gamma
                  (fun uu___221_11051  ->
                     match uu___221_11051 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11090 = FStar_Ident.lid_equals lid l  in
                         if uu____11090
                         then
                           let uu____11111 =
                             let uu____11130 =
                               let uu____11145 = inst_tscheme t  in
                               FStar_Util.Inl uu____11145  in
                             let uu____11160 = FStar_Ident.range_of_lid l  in
                             (uu____11130, uu____11160)  in
                           FStar_Pervasives_Native.Some uu____11111
                         else FStar_Pervasives_Native.None
                     | uu____11212 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11007
                (fun uu____11250  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___222_11259  ->
                        match uu___222_11259 with
                        | (uu____11262,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11264);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11265;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11266;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11267;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11268;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11288 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11288
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
                                  uu____11336 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11343 -> cache t  in
                            let uu____11344 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11344 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11350 =
                                   let uu____11351 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11351)
                                    in
                                 maybe_cache uu____11350)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11419 = find_in_sigtab env lid  in
         match uu____11419 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11506) ->
          add_sigelts env ses
      | uu____11515 ->
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
            | uu____11529 -> ()))

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
        (fun uu___223_11560  ->
           match uu___223_11560 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11578 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11639,lb::[]),uu____11641) ->
            let uu____11648 =
              let uu____11657 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11666 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11657, uu____11666)  in
            FStar_Pervasives_Native.Some uu____11648
        | FStar_Syntax_Syntax.Sig_let ((uu____11679,lbs),uu____11681) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11711 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11723 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11723
                     then
                       let uu____11734 =
                         let uu____11743 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11752 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11743, uu____11752)  in
                       FStar_Pervasives_Native.Some uu____11734
                     else FStar_Pervasives_Native.None)
        | uu____11774 -> FStar_Pervasives_Native.None
  
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
          let uu____11833 =
            let uu____11842 =
              let uu____11847 =
                let uu____11848 =
                  let uu____11851 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11851
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11848)  in
              inst_tscheme1 uu____11847  in
            (uu____11842, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11833
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11873,uu____11874) ->
          let uu____11879 =
            let uu____11888 =
              let uu____11893 =
                let uu____11894 =
                  let uu____11897 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11897  in
                (us, uu____11894)  in
              inst_tscheme1 uu____11893  in
            (uu____11888, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11879
      | uu____11916 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12004 =
          match uu____12004 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12100,uvs,t,uu____12103,uu____12104,uu____12105);
                      FStar_Syntax_Syntax.sigrng = uu____12106;
                      FStar_Syntax_Syntax.sigquals = uu____12107;
                      FStar_Syntax_Syntax.sigmeta = uu____12108;
                      FStar_Syntax_Syntax.sigattrs = uu____12109;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12130 =
                     let uu____12139 = inst_tscheme1 (uvs, t)  in
                     (uu____12139, rng)  in
                   FStar_Pervasives_Native.Some uu____12130
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12163;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12165;
                      FStar_Syntax_Syntax.sigattrs = uu____12166;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12183 =
                     let uu____12184 = in_cur_mod env l  in uu____12184 = Yes
                      in
                   if uu____12183
                   then
                     let uu____12195 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12195
                      then
                        let uu____12208 =
                          let uu____12217 = inst_tscheme1 (uvs, t)  in
                          (uu____12217, rng)  in
                        FStar_Pervasives_Native.Some uu____12208
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12248 =
                        let uu____12257 = inst_tscheme1 (uvs, t)  in
                        (uu____12257, rng)  in
                      FStar_Pervasives_Native.Some uu____12248)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12282,uu____12283);
                      FStar_Syntax_Syntax.sigrng = uu____12284;
                      FStar_Syntax_Syntax.sigquals = uu____12285;
                      FStar_Syntax_Syntax.sigmeta = uu____12286;
                      FStar_Syntax_Syntax.sigattrs = uu____12287;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12326 =
                          let uu____12335 = inst_tscheme1 (uvs, k)  in
                          (uu____12335, rng)  in
                        FStar_Pervasives_Native.Some uu____12326
                    | uu____12356 ->
                        let uu____12357 =
                          let uu____12366 =
                            let uu____12371 =
                              let uu____12372 =
                                let uu____12375 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12375
                                 in
                              (uvs, uu____12372)  in
                            inst_tscheme1 uu____12371  in
                          (uu____12366, rng)  in
                        FStar_Pervasives_Native.Some uu____12357)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12398,uu____12399);
                      FStar_Syntax_Syntax.sigrng = uu____12400;
                      FStar_Syntax_Syntax.sigquals = uu____12401;
                      FStar_Syntax_Syntax.sigmeta = uu____12402;
                      FStar_Syntax_Syntax.sigattrs = uu____12403;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12443 =
                          let uu____12452 = inst_tscheme_with (uvs, k) us  in
                          (uu____12452, rng)  in
                        FStar_Pervasives_Native.Some uu____12443
                    | uu____12473 ->
                        let uu____12474 =
                          let uu____12483 =
                            let uu____12488 =
                              let uu____12489 =
                                let uu____12492 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12492
                                 in
                              (uvs, uu____12489)  in
                            inst_tscheme_with uu____12488 us  in
                          (uu____12483, rng)  in
                        FStar_Pervasives_Native.Some uu____12474)
               | FStar_Util.Inr se ->
                   let uu____12528 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12549;
                          FStar_Syntax_Syntax.sigrng = uu____12550;
                          FStar_Syntax_Syntax.sigquals = uu____12551;
                          FStar_Syntax_Syntax.sigmeta = uu____12552;
                          FStar_Syntax_Syntax.sigattrs = uu____12553;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12568 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12528
                     (FStar_Util.map_option
                        (fun uu____12616  ->
                           match uu____12616 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12647 =
          let uu____12658 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12658 mapper  in
        match uu____12647 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12732 =
              let uu____12743 =
                let uu____12750 =
                  let uu___243_12753 = t  in
                  let uu____12754 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___243_12753.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12754;
                    FStar_Syntax_Syntax.vars =
                      (uu___243_12753.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12750)  in
              (uu____12743, r)  in
            FStar_Pervasives_Native.Some uu____12732
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12801 = lookup_qname env l  in
      match uu____12801 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12820 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12872 = try_lookup_bv env bv  in
      match uu____12872 with
      | FStar_Pervasives_Native.None  ->
          let uu____12887 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12887 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12902 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12903 =
            let uu____12904 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12904  in
          (uu____12902, uu____12903)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12925 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12925 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12991 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12991  in
          let uu____12992 =
            let uu____13001 =
              let uu____13006 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13006)  in
            (uu____13001, r1)  in
          FStar_Pervasives_Native.Some uu____12992
  
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
        let uu____13040 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13040 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13073,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13098 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13098  in
            let uu____13099 =
              let uu____13104 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13104, r1)  in
            FStar_Pervasives_Native.Some uu____13099
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13127 = try_lookup_lid env l  in
      match uu____13127 with
      | FStar_Pervasives_Native.None  ->
          let uu____13154 = name_not_found l  in
          let uu____13159 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13154 uu____13159
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___224_13199  ->
              match uu___224_13199 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13201 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13220 = lookup_qname env lid  in
      match uu____13220 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13229,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13232;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13234;
              FStar_Syntax_Syntax.sigattrs = uu____13235;_},FStar_Pervasives_Native.None
            ),uu____13236)
          ->
          let uu____13285 =
            let uu____13292 =
              let uu____13293 =
                let uu____13296 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13296 t  in
              (uvs, uu____13293)  in
            (uu____13292, q)  in
          FStar_Pervasives_Native.Some uu____13285
      | uu____13309 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13330 = lookup_qname env lid  in
      match uu____13330 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13335,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13338;
              FStar_Syntax_Syntax.sigquals = uu____13339;
              FStar_Syntax_Syntax.sigmeta = uu____13340;
              FStar_Syntax_Syntax.sigattrs = uu____13341;_},FStar_Pervasives_Native.None
            ),uu____13342)
          ->
          let uu____13391 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13391 (uvs, t)
      | uu____13396 ->
          let uu____13397 = name_not_found lid  in
          let uu____13402 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13397 uu____13402
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13421 = lookup_qname env lid  in
      match uu____13421 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13426,uvs,t,uu____13429,uu____13430,uu____13431);
              FStar_Syntax_Syntax.sigrng = uu____13432;
              FStar_Syntax_Syntax.sigquals = uu____13433;
              FStar_Syntax_Syntax.sigmeta = uu____13434;
              FStar_Syntax_Syntax.sigattrs = uu____13435;_},FStar_Pervasives_Native.None
            ),uu____13436)
          ->
          let uu____13489 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13489 (uvs, t)
      | uu____13494 ->
          let uu____13495 = name_not_found lid  in
          let uu____13500 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13495 uu____13500
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13521 = lookup_qname env lid  in
      match uu____13521 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13528,uu____13529,uu____13530,uu____13531,uu____13532,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13534;
              FStar_Syntax_Syntax.sigquals = uu____13535;
              FStar_Syntax_Syntax.sigmeta = uu____13536;
              FStar_Syntax_Syntax.sigattrs = uu____13537;_},uu____13538),uu____13539)
          -> (true, dcs)
      | uu____13600 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13613 = lookup_qname env lid  in
      match uu____13613 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13614,uu____13615,uu____13616,l,uu____13618,uu____13619);
              FStar_Syntax_Syntax.sigrng = uu____13620;
              FStar_Syntax_Syntax.sigquals = uu____13621;
              FStar_Syntax_Syntax.sigmeta = uu____13622;
              FStar_Syntax_Syntax.sigattrs = uu____13623;_},uu____13624),uu____13625)
          -> l
      | uu____13680 ->
          let uu____13681 =
            let uu____13682 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13682  in
          failwith uu____13681
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13731)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13782,lbs),uu____13784)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13806 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13806
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13838 -> FStar_Pervasives_Native.None)
        | uu____13843 -> FStar_Pervasives_Native.None
  
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
        let uu____13873 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13873
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13898),uu____13899) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13948 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13969 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13969
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13988 = lookup_qname env ftv  in
      match uu____13988 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13992) ->
          let uu____14037 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14037 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14058,t),r) ->
               let uu____14073 =
                 let uu____14074 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14074 t  in
               FStar_Pervasives_Native.Some uu____14073)
      | uu____14075 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14086 = try_lookup_effect_lid env ftv  in
      match uu____14086 with
      | FStar_Pervasives_Native.None  ->
          let uu____14089 = name_not_found ftv  in
          let uu____14094 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14089 uu____14094
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
        let uu____14117 = lookup_qname env lid0  in
        match uu____14117 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14128);
                FStar_Syntax_Syntax.sigrng = uu____14129;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14131;
                FStar_Syntax_Syntax.sigattrs = uu____14132;_},FStar_Pervasives_Native.None
              ),uu____14133)
            ->
            let lid1 =
              let uu____14187 =
                let uu____14188 = FStar_Ident.range_of_lid lid  in
                let uu____14189 =
                  let uu____14190 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14190  in
                FStar_Range.set_use_range uu____14188 uu____14189  in
              FStar_Ident.set_lid_range lid uu____14187  in
            let uu____14191 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___225_14195  ->
                      match uu___225_14195 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14196 -> false))
               in
            if uu____14191
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14210 =
                      let uu____14211 =
                        let uu____14212 = get_range env  in
                        FStar_Range.string_of_range uu____14212  in
                      let uu____14213 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14214 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14211 uu____14213 uu____14214
                       in
                    failwith uu____14210)
                  in
               match (binders, univs1) with
               | ([],uu____14229) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14250,uu____14251::uu____14252::uu____14253) ->
                   let uu____14270 =
                     let uu____14271 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14272 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14271 uu____14272
                      in
                   failwith uu____14270
               | uu____14279 ->
                   let uu____14292 =
                     let uu____14297 =
                       let uu____14298 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14298)  in
                     inst_tscheme_with uu____14297 insts  in
                   (match uu____14292 with
                    | (uu____14311,t) ->
                        let t1 =
                          let uu____14314 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14314 t  in
                        let uu____14315 =
                          let uu____14316 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14316.FStar_Syntax_Syntax.n  in
                        (match uu____14315 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14347 -> failwith "Impossible")))
        | uu____14354 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14377 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14377 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14390,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14397 = find1 l2  in
            (match uu____14397 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14404 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14404 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14408 = find1 l  in
            (match uu____14408 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14413 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14413
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14427 = lookup_qname env l1  in
      match uu____14427 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14430;
              FStar_Syntax_Syntax.sigrng = uu____14431;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14433;
              FStar_Syntax_Syntax.sigattrs = uu____14434;_},uu____14435),uu____14436)
          -> q
      | uu____14487 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14508 =
          let uu____14509 =
            let uu____14510 = FStar_Util.string_of_int i  in
            let uu____14511 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14510 uu____14511
             in
          failwith uu____14509  in
        let uu____14512 = lookup_datacon env lid  in
        match uu____14512 with
        | (uu____14517,t) ->
            let uu____14519 =
              let uu____14520 = FStar_Syntax_Subst.compress t  in
              uu____14520.FStar_Syntax_Syntax.n  in
            (match uu____14519 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14524) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14555 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14555
                      FStar_Pervasives_Native.fst)
             | uu____14564 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14575 = lookup_qname env l  in
      match uu____14575 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14576,uu____14577,uu____14578);
              FStar_Syntax_Syntax.sigrng = uu____14579;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14581;
              FStar_Syntax_Syntax.sigattrs = uu____14582;_},uu____14583),uu____14584)
          ->
          FStar_Util.for_some
            (fun uu___226_14637  ->
               match uu___226_14637 with
               | FStar_Syntax_Syntax.Projector uu____14638 -> true
               | uu____14643 -> false) quals
      | uu____14644 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14655 = lookup_qname env lid  in
      match uu____14655 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14656,uu____14657,uu____14658,uu____14659,uu____14660,uu____14661);
              FStar_Syntax_Syntax.sigrng = uu____14662;
              FStar_Syntax_Syntax.sigquals = uu____14663;
              FStar_Syntax_Syntax.sigmeta = uu____14664;
              FStar_Syntax_Syntax.sigattrs = uu____14665;_},uu____14666),uu____14667)
          -> true
      | uu____14722 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14733 = lookup_qname env lid  in
      match uu____14733 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14734,uu____14735,uu____14736,uu____14737,uu____14738,uu____14739);
              FStar_Syntax_Syntax.sigrng = uu____14740;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14742;
              FStar_Syntax_Syntax.sigattrs = uu____14743;_},uu____14744),uu____14745)
          ->
          FStar_Util.for_some
            (fun uu___227_14806  ->
               match uu___227_14806 with
               | FStar_Syntax_Syntax.RecordType uu____14807 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14816 -> true
               | uu____14825 -> false) quals
      | uu____14826 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14832,uu____14833);
            FStar_Syntax_Syntax.sigrng = uu____14834;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14836;
            FStar_Syntax_Syntax.sigattrs = uu____14837;_},uu____14838),uu____14839)
        ->
        FStar_Util.for_some
          (fun uu___228_14896  ->
             match uu___228_14896 with
             | FStar_Syntax_Syntax.Action uu____14897 -> true
             | uu____14898 -> false) quals
    | uu____14899 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14910 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14910
  
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
      let uu____14924 =
        let uu____14925 = FStar_Syntax_Util.un_uinst head1  in
        uu____14925.FStar_Syntax_Syntax.n  in
      match uu____14924 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14929 ->
               true
           | uu____14930 -> false)
      | uu____14931 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14942 = lookup_qname env l  in
      match uu____14942 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14944),uu____14945) ->
          FStar_Util.for_some
            (fun uu___229_14993  ->
               match uu___229_14993 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14994 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14995 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15066 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15082) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15099 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15106 ->
                 FStar_Pervasives_Native.Some true
             | uu____15123 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15124 =
        let uu____15127 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15127 mapper  in
      match uu____15124 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15177 = lookup_qname env lid  in
      match uu____15177 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15178,uu____15179,tps,uu____15181,uu____15182,uu____15183);
              FStar_Syntax_Syntax.sigrng = uu____15184;
              FStar_Syntax_Syntax.sigquals = uu____15185;
              FStar_Syntax_Syntax.sigmeta = uu____15186;
              FStar_Syntax_Syntax.sigattrs = uu____15187;_},uu____15188),uu____15189)
          -> FStar_List.length tps
      | uu____15252 ->
          let uu____15253 = name_not_found lid  in
          let uu____15258 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15253 uu____15258
  
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
           (fun uu____15302  ->
              match uu____15302 with
              | (d,uu____15310) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15325 = effect_decl_opt env l  in
      match uu____15325 with
      | FStar_Pervasives_Native.None  ->
          let uu____15340 = name_not_found l  in
          let uu____15345 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15340 uu____15345
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15367  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15386  ->
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
        let uu____15417 = FStar_Ident.lid_equals l1 l2  in
        if uu____15417
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15425 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15425
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15433 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15486  ->
                        match uu____15486 with
                        | (m1,m2,uu____15499,uu____15500,uu____15501) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15433 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15518 =
                    let uu____15523 =
                      let uu____15524 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15525 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15524
                        uu____15525
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15523)
                     in
                  FStar_Errors.raise_error uu____15518 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15532,uu____15533,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15566 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15566
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
  'Auu____15582 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15582)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15611 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15637  ->
                match uu____15637 with
                | (d,uu____15643) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15611 with
      | FStar_Pervasives_Native.None  ->
          let uu____15654 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15654
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15667 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15667 with
           | (uu____15682,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15698)::(wp,uu____15700)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15736 -> failwith "Impossible"))
  
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
          let uu____15789 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15789
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15791 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15791
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
                  let uu____15799 = get_range env  in
                  let uu____15800 =
                    let uu____15807 =
                      let uu____15808 =
                        let uu____15823 =
                          let uu____15832 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15832]  in
                        (null_wp, uu____15823)  in
                      FStar_Syntax_Syntax.Tm_app uu____15808  in
                    FStar_Syntax_Syntax.mk uu____15807  in
                  uu____15800 FStar_Pervasives_Native.None uu____15799  in
                let uu____15864 =
                  let uu____15865 =
                    let uu____15874 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15874]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15865;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15864))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___244_15905 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___244_15905.order);
              joins = (uu___244_15905.joins)
            }  in
          let uu___245_15914 = env  in
          {
            solver = (uu___245_15914.solver);
            range = (uu___245_15914.range);
            curmodule = (uu___245_15914.curmodule);
            gamma = (uu___245_15914.gamma);
            gamma_sig = (uu___245_15914.gamma_sig);
            gamma_cache = (uu___245_15914.gamma_cache);
            modules = (uu___245_15914.modules);
            expected_typ = (uu___245_15914.expected_typ);
            sigtab = (uu___245_15914.sigtab);
            is_pattern = (uu___245_15914.is_pattern);
            instantiate_imp = (uu___245_15914.instantiate_imp);
            effects;
            generalize = (uu___245_15914.generalize);
            letrecs = (uu___245_15914.letrecs);
            top_level = (uu___245_15914.top_level);
            check_uvars = (uu___245_15914.check_uvars);
            use_eq = (uu___245_15914.use_eq);
            is_iface = (uu___245_15914.is_iface);
            admit = (uu___245_15914.admit);
            lax = (uu___245_15914.lax);
            lax_universes = (uu___245_15914.lax_universes);
            phase1 = (uu___245_15914.phase1);
            failhard = (uu___245_15914.failhard);
            nosynth = (uu___245_15914.nosynth);
            uvar_subtyping = (uu___245_15914.uvar_subtyping);
            tc_term = (uu___245_15914.tc_term);
            type_of = (uu___245_15914.type_of);
            universe_of = (uu___245_15914.universe_of);
            check_type_of = (uu___245_15914.check_type_of);
            use_bv_sorts = (uu___245_15914.use_bv_sorts);
            qtbl_name_and_index = (uu___245_15914.qtbl_name_and_index);
            normalized_eff_names = (uu___245_15914.normalized_eff_names);
            proof_ns = (uu___245_15914.proof_ns);
            synth_hook = (uu___245_15914.synth_hook);
            splice = (uu___245_15914.splice);
            is_native_tactic = (uu___245_15914.is_native_tactic);
            identifier_info = (uu___245_15914.identifier_info);
            tc_hooks = (uu___245_15914.tc_hooks);
            dsenv = (uu___245_15914.dsenv);
            dep_graph = (uu___245_15914.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15944 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15944  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16102 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16103 = l1 u t wp e  in
                                l2 u t uu____16102 uu____16103))
                | uu____16104 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16176 = inst_tscheme_with lift_t [u]  in
            match uu____16176 with
            | (uu____16183,lift_t1) ->
                let uu____16185 =
                  let uu____16192 =
                    let uu____16193 =
                      let uu____16208 =
                        let uu____16217 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16224 =
                          let uu____16233 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16233]  in
                        uu____16217 :: uu____16224  in
                      (lift_t1, uu____16208)  in
                    FStar_Syntax_Syntax.Tm_app uu____16193  in
                  FStar_Syntax_Syntax.mk uu____16192  in
                uu____16185 FStar_Pervasives_Native.None
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
            let uu____16335 = inst_tscheme_with lift_t [u]  in
            match uu____16335 with
            | (uu____16342,lift_t1) ->
                let uu____16344 =
                  let uu____16351 =
                    let uu____16352 =
                      let uu____16367 =
                        let uu____16376 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16383 =
                          let uu____16392 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16399 =
                            let uu____16408 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16408]  in
                          uu____16392 :: uu____16399  in
                        uu____16376 :: uu____16383  in
                      (lift_t1, uu____16367)  in
                    FStar_Syntax_Syntax.Tm_app uu____16352  in
                  FStar_Syntax_Syntax.mk uu____16351  in
                uu____16344 FStar_Pervasives_Native.None
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
              let uu____16498 =
                let uu____16499 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16499
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16498  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16503 =
              let uu____16504 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16504  in
            let uu____16505 =
              let uu____16506 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16532 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16532)
                 in
              FStar_Util.dflt "none" uu____16506  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16503
              uu____16505
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16558  ->
                    match uu____16558 with
                    | (e,uu____16566) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16589 =
            match uu____16589 with
            | (i,j) ->
                let uu____16600 = FStar_Ident.lid_equals i j  in
                if uu____16600
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
              let uu____16632 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16642 = FStar_Ident.lid_equals i k  in
                        if uu____16642
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16653 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16653
                                  then []
                                  else
                                    (let uu____16657 =
                                       let uu____16666 =
                                         find_edge order1 (i, k)  in
                                       let uu____16669 =
                                         find_edge order1 (k, j)  in
                                       (uu____16666, uu____16669)  in
                                     match uu____16657 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16684 =
                                           compose_edges e1 e2  in
                                         [uu____16684]
                                     | uu____16685 -> [])))))
                 in
              FStar_List.append order1 uu____16632  in
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
                   let uu____16715 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16717 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16717
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16715
                   then
                     let uu____16722 =
                       let uu____16727 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16727)
                        in
                     let uu____16728 = get_range env  in
                     FStar_Errors.raise_error uu____16722 uu____16728
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16805 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16805
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16854 =
                                              let uu____16863 =
                                                find_edge order2 (i, k)  in
                                              let uu____16866 =
                                                find_edge order2 (j, k)  in
                                              (uu____16863, uu____16866)  in
                                            match uu____16854 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16908,uu____16909)
                                                     ->
                                                     let uu____16916 =
                                                       let uu____16921 =
                                                         let uu____16922 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16922
                                                          in
                                                       let uu____16925 =
                                                         let uu____16926 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16926
                                                          in
                                                       (uu____16921,
                                                         uu____16925)
                                                        in
                                                     (match uu____16916 with
                                                      | (true ,true ) ->
                                                          let uu____16937 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16937
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
                                            | uu____16962 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___246_17035 = env.effects  in
              { decls = (uu___246_17035.decls); order = order2; joins }  in
            let uu___247_17036 = env  in
            {
              solver = (uu___247_17036.solver);
              range = (uu___247_17036.range);
              curmodule = (uu___247_17036.curmodule);
              gamma = (uu___247_17036.gamma);
              gamma_sig = (uu___247_17036.gamma_sig);
              gamma_cache = (uu___247_17036.gamma_cache);
              modules = (uu___247_17036.modules);
              expected_typ = (uu___247_17036.expected_typ);
              sigtab = (uu___247_17036.sigtab);
              is_pattern = (uu___247_17036.is_pattern);
              instantiate_imp = (uu___247_17036.instantiate_imp);
              effects;
              generalize = (uu___247_17036.generalize);
              letrecs = (uu___247_17036.letrecs);
              top_level = (uu___247_17036.top_level);
              check_uvars = (uu___247_17036.check_uvars);
              use_eq = (uu___247_17036.use_eq);
              is_iface = (uu___247_17036.is_iface);
              admit = (uu___247_17036.admit);
              lax = (uu___247_17036.lax);
              lax_universes = (uu___247_17036.lax_universes);
              phase1 = (uu___247_17036.phase1);
              failhard = (uu___247_17036.failhard);
              nosynth = (uu___247_17036.nosynth);
              uvar_subtyping = (uu___247_17036.uvar_subtyping);
              tc_term = (uu___247_17036.tc_term);
              type_of = (uu___247_17036.type_of);
              universe_of = (uu___247_17036.universe_of);
              check_type_of = (uu___247_17036.check_type_of);
              use_bv_sorts = (uu___247_17036.use_bv_sorts);
              qtbl_name_and_index = (uu___247_17036.qtbl_name_and_index);
              normalized_eff_names = (uu___247_17036.normalized_eff_names);
              proof_ns = (uu___247_17036.proof_ns);
              synth_hook = (uu___247_17036.synth_hook);
              splice = (uu___247_17036.splice);
              is_native_tactic = (uu___247_17036.is_native_tactic);
              identifier_info = (uu___247_17036.identifier_info);
              tc_hooks = (uu___247_17036.tc_hooks);
              dsenv = (uu___247_17036.dsenv);
              dep_graph = (uu___247_17036.dep_graph)
            }))
      | uu____17037 -> env
  
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
        | uu____17065 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17077 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17077 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17094 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17094 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17112 =
                     let uu____17117 =
                       let uu____17118 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17123 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17130 =
                         let uu____17131 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17131  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17118 uu____17123 uu____17130
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17117)
                      in
                   FStar_Errors.raise_error uu____17112
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17136 =
                     let uu____17145 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17145 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17174  ->
                        fun uu____17175  ->
                          match (uu____17174, uu____17175) with
                          | ((x,uu____17197),(t,uu____17199)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17136
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____17218 =
                     let uu___248_17219 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___248_17219.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___248_17219.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___248_17219.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___248_17219.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____17218
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
          let uu____17249 = effect_decl_opt env effect_name  in
          match uu____17249 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17282 =
                only_reifiable &&
                  (let uu____17284 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17284)
                 in
              if uu____17282
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17300 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____17319 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____17348 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____17348
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____17349 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____17349
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____17361 =
                       let uu____17364 = get_range env  in
                       let uu____17365 =
                         let uu____17372 =
                           let uu____17373 =
                             let uu____17388 =
                               let uu____17397 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17397; wp]  in
                             (repr, uu____17388)  in
                           FStar_Syntax_Syntax.Tm_app uu____17373  in
                         FStar_Syntax_Syntax.mk uu____17372  in
                       uu____17365 FStar_Pervasives_Native.None uu____17364
                        in
                     FStar_Pervasives_Native.Some uu____17361)
  
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
          let uu____17477 =
            let uu____17482 =
              let uu____17483 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17483
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17482)  in
          let uu____17484 = get_range env  in
          FStar_Errors.raise_error uu____17477 uu____17484  in
        let uu____17485 = effect_repr_aux true env c u_c  in
        match uu____17485 with
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
      | uu____17531 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17542 =
        let uu____17543 = FStar_Syntax_Subst.compress t  in
        uu____17543.FStar_Syntax_Syntax.n  in
      match uu____17542 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17546,c) ->
          is_reifiable_comp env c
      | uu____17564 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___249_17585 = env  in
        {
          solver = (uu___249_17585.solver);
          range = (uu___249_17585.range);
          curmodule = (uu___249_17585.curmodule);
          gamma = (uu___249_17585.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___249_17585.gamma_cache);
          modules = (uu___249_17585.modules);
          expected_typ = (uu___249_17585.expected_typ);
          sigtab = (uu___249_17585.sigtab);
          is_pattern = (uu___249_17585.is_pattern);
          instantiate_imp = (uu___249_17585.instantiate_imp);
          effects = (uu___249_17585.effects);
          generalize = (uu___249_17585.generalize);
          letrecs = (uu___249_17585.letrecs);
          top_level = (uu___249_17585.top_level);
          check_uvars = (uu___249_17585.check_uvars);
          use_eq = (uu___249_17585.use_eq);
          is_iface = (uu___249_17585.is_iface);
          admit = (uu___249_17585.admit);
          lax = (uu___249_17585.lax);
          lax_universes = (uu___249_17585.lax_universes);
          phase1 = (uu___249_17585.phase1);
          failhard = (uu___249_17585.failhard);
          nosynth = (uu___249_17585.nosynth);
          uvar_subtyping = (uu___249_17585.uvar_subtyping);
          tc_term = (uu___249_17585.tc_term);
          type_of = (uu___249_17585.type_of);
          universe_of = (uu___249_17585.universe_of);
          check_type_of = (uu___249_17585.check_type_of);
          use_bv_sorts = (uu___249_17585.use_bv_sorts);
          qtbl_name_and_index = (uu___249_17585.qtbl_name_and_index);
          normalized_eff_names = (uu___249_17585.normalized_eff_names);
          proof_ns = (uu___249_17585.proof_ns);
          synth_hook = (uu___249_17585.synth_hook);
          splice = (uu___249_17585.splice);
          is_native_tactic = (uu___249_17585.is_native_tactic);
          identifier_info = (uu___249_17585.identifier_info);
          tc_hooks = (uu___249_17585.tc_hooks);
          dsenv = (uu___249_17585.dsenv);
          dep_graph = (uu___249_17585.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___250_17597 = env  in
      {
        solver = (uu___250_17597.solver);
        range = (uu___250_17597.range);
        curmodule = (uu___250_17597.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___250_17597.gamma_sig);
        gamma_cache = (uu___250_17597.gamma_cache);
        modules = (uu___250_17597.modules);
        expected_typ = (uu___250_17597.expected_typ);
        sigtab = (uu___250_17597.sigtab);
        is_pattern = (uu___250_17597.is_pattern);
        instantiate_imp = (uu___250_17597.instantiate_imp);
        effects = (uu___250_17597.effects);
        generalize = (uu___250_17597.generalize);
        letrecs = (uu___250_17597.letrecs);
        top_level = (uu___250_17597.top_level);
        check_uvars = (uu___250_17597.check_uvars);
        use_eq = (uu___250_17597.use_eq);
        is_iface = (uu___250_17597.is_iface);
        admit = (uu___250_17597.admit);
        lax = (uu___250_17597.lax);
        lax_universes = (uu___250_17597.lax_universes);
        phase1 = (uu___250_17597.phase1);
        failhard = (uu___250_17597.failhard);
        nosynth = (uu___250_17597.nosynth);
        uvar_subtyping = (uu___250_17597.uvar_subtyping);
        tc_term = (uu___250_17597.tc_term);
        type_of = (uu___250_17597.type_of);
        universe_of = (uu___250_17597.universe_of);
        check_type_of = (uu___250_17597.check_type_of);
        use_bv_sorts = (uu___250_17597.use_bv_sorts);
        qtbl_name_and_index = (uu___250_17597.qtbl_name_and_index);
        normalized_eff_names = (uu___250_17597.normalized_eff_names);
        proof_ns = (uu___250_17597.proof_ns);
        synth_hook = (uu___250_17597.synth_hook);
        splice = (uu___250_17597.splice);
        is_native_tactic = (uu___250_17597.is_native_tactic);
        identifier_info = (uu___250_17597.identifier_info);
        tc_hooks = (uu___250_17597.tc_hooks);
        dsenv = (uu___250_17597.dsenv);
        dep_graph = (uu___250_17597.dep_graph)
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
            (let uu___251_17652 = env  in
             {
               solver = (uu___251_17652.solver);
               range = (uu___251_17652.range);
               curmodule = (uu___251_17652.curmodule);
               gamma = rest;
               gamma_sig = (uu___251_17652.gamma_sig);
               gamma_cache = (uu___251_17652.gamma_cache);
               modules = (uu___251_17652.modules);
               expected_typ = (uu___251_17652.expected_typ);
               sigtab = (uu___251_17652.sigtab);
               is_pattern = (uu___251_17652.is_pattern);
               instantiate_imp = (uu___251_17652.instantiate_imp);
               effects = (uu___251_17652.effects);
               generalize = (uu___251_17652.generalize);
               letrecs = (uu___251_17652.letrecs);
               top_level = (uu___251_17652.top_level);
               check_uvars = (uu___251_17652.check_uvars);
               use_eq = (uu___251_17652.use_eq);
               is_iface = (uu___251_17652.is_iface);
               admit = (uu___251_17652.admit);
               lax = (uu___251_17652.lax);
               lax_universes = (uu___251_17652.lax_universes);
               phase1 = (uu___251_17652.phase1);
               failhard = (uu___251_17652.failhard);
               nosynth = (uu___251_17652.nosynth);
               uvar_subtyping = (uu___251_17652.uvar_subtyping);
               tc_term = (uu___251_17652.tc_term);
               type_of = (uu___251_17652.type_of);
               universe_of = (uu___251_17652.universe_of);
               check_type_of = (uu___251_17652.check_type_of);
               use_bv_sorts = (uu___251_17652.use_bv_sorts);
               qtbl_name_and_index = (uu___251_17652.qtbl_name_and_index);
               normalized_eff_names = (uu___251_17652.normalized_eff_names);
               proof_ns = (uu___251_17652.proof_ns);
               synth_hook = (uu___251_17652.synth_hook);
               splice = (uu___251_17652.splice);
               is_native_tactic = (uu___251_17652.is_native_tactic);
               identifier_info = (uu___251_17652.identifier_info);
               tc_hooks = (uu___251_17652.tc_hooks);
               dsenv = (uu___251_17652.dsenv);
               dep_graph = (uu___251_17652.dep_graph)
             }))
    | uu____17653 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17679  ->
             match uu____17679 with | (x,uu____17685) -> push_bv env1 x) env
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
            let uu___252_17715 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___252_17715.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___252_17715.FStar_Syntax_Syntax.index);
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
      (let uu___253_17755 = env  in
       {
         solver = (uu___253_17755.solver);
         range = (uu___253_17755.range);
         curmodule = (uu___253_17755.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___253_17755.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___253_17755.sigtab);
         is_pattern = (uu___253_17755.is_pattern);
         instantiate_imp = (uu___253_17755.instantiate_imp);
         effects = (uu___253_17755.effects);
         generalize = (uu___253_17755.generalize);
         letrecs = (uu___253_17755.letrecs);
         top_level = (uu___253_17755.top_level);
         check_uvars = (uu___253_17755.check_uvars);
         use_eq = (uu___253_17755.use_eq);
         is_iface = (uu___253_17755.is_iface);
         admit = (uu___253_17755.admit);
         lax = (uu___253_17755.lax);
         lax_universes = (uu___253_17755.lax_universes);
         phase1 = (uu___253_17755.phase1);
         failhard = (uu___253_17755.failhard);
         nosynth = (uu___253_17755.nosynth);
         uvar_subtyping = (uu___253_17755.uvar_subtyping);
         tc_term = (uu___253_17755.tc_term);
         type_of = (uu___253_17755.type_of);
         universe_of = (uu___253_17755.universe_of);
         check_type_of = (uu___253_17755.check_type_of);
         use_bv_sorts = (uu___253_17755.use_bv_sorts);
         qtbl_name_and_index = (uu___253_17755.qtbl_name_and_index);
         normalized_eff_names = (uu___253_17755.normalized_eff_names);
         proof_ns = (uu___253_17755.proof_ns);
         synth_hook = (uu___253_17755.synth_hook);
         splice = (uu___253_17755.splice);
         is_native_tactic = (uu___253_17755.is_native_tactic);
         identifier_info = (uu___253_17755.identifier_info);
         tc_hooks = (uu___253_17755.tc_hooks);
         dsenv = (uu___253_17755.dsenv);
         dep_graph = (uu___253_17755.dep_graph)
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
        let uu____17797 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17797 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17825 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17825)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___254_17840 = env  in
      {
        solver = (uu___254_17840.solver);
        range = (uu___254_17840.range);
        curmodule = (uu___254_17840.curmodule);
        gamma = (uu___254_17840.gamma);
        gamma_sig = (uu___254_17840.gamma_sig);
        gamma_cache = (uu___254_17840.gamma_cache);
        modules = (uu___254_17840.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___254_17840.sigtab);
        is_pattern = (uu___254_17840.is_pattern);
        instantiate_imp = (uu___254_17840.instantiate_imp);
        effects = (uu___254_17840.effects);
        generalize = (uu___254_17840.generalize);
        letrecs = (uu___254_17840.letrecs);
        top_level = (uu___254_17840.top_level);
        check_uvars = (uu___254_17840.check_uvars);
        use_eq = false;
        is_iface = (uu___254_17840.is_iface);
        admit = (uu___254_17840.admit);
        lax = (uu___254_17840.lax);
        lax_universes = (uu___254_17840.lax_universes);
        phase1 = (uu___254_17840.phase1);
        failhard = (uu___254_17840.failhard);
        nosynth = (uu___254_17840.nosynth);
        uvar_subtyping = (uu___254_17840.uvar_subtyping);
        tc_term = (uu___254_17840.tc_term);
        type_of = (uu___254_17840.type_of);
        universe_of = (uu___254_17840.universe_of);
        check_type_of = (uu___254_17840.check_type_of);
        use_bv_sorts = (uu___254_17840.use_bv_sorts);
        qtbl_name_and_index = (uu___254_17840.qtbl_name_and_index);
        normalized_eff_names = (uu___254_17840.normalized_eff_names);
        proof_ns = (uu___254_17840.proof_ns);
        synth_hook = (uu___254_17840.synth_hook);
        splice = (uu___254_17840.splice);
        is_native_tactic = (uu___254_17840.is_native_tactic);
        identifier_info = (uu___254_17840.identifier_info);
        tc_hooks = (uu___254_17840.tc_hooks);
        dsenv = (uu___254_17840.dsenv);
        dep_graph = (uu___254_17840.dep_graph)
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
    let uu____17868 = expected_typ env_  in
    ((let uu___255_17874 = env_  in
      {
        solver = (uu___255_17874.solver);
        range = (uu___255_17874.range);
        curmodule = (uu___255_17874.curmodule);
        gamma = (uu___255_17874.gamma);
        gamma_sig = (uu___255_17874.gamma_sig);
        gamma_cache = (uu___255_17874.gamma_cache);
        modules = (uu___255_17874.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___255_17874.sigtab);
        is_pattern = (uu___255_17874.is_pattern);
        instantiate_imp = (uu___255_17874.instantiate_imp);
        effects = (uu___255_17874.effects);
        generalize = (uu___255_17874.generalize);
        letrecs = (uu___255_17874.letrecs);
        top_level = (uu___255_17874.top_level);
        check_uvars = (uu___255_17874.check_uvars);
        use_eq = false;
        is_iface = (uu___255_17874.is_iface);
        admit = (uu___255_17874.admit);
        lax = (uu___255_17874.lax);
        lax_universes = (uu___255_17874.lax_universes);
        phase1 = (uu___255_17874.phase1);
        failhard = (uu___255_17874.failhard);
        nosynth = (uu___255_17874.nosynth);
        uvar_subtyping = (uu___255_17874.uvar_subtyping);
        tc_term = (uu___255_17874.tc_term);
        type_of = (uu___255_17874.type_of);
        universe_of = (uu___255_17874.universe_of);
        check_type_of = (uu___255_17874.check_type_of);
        use_bv_sorts = (uu___255_17874.use_bv_sorts);
        qtbl_name_and_index = (uu___255_17874.qtbl_name_and_index);
        normalized_eff_names = (uu___255_17874.normalized_eff_names);
        proof_ns = (uu___255_17874.proof_ns);
        synth_hook = (uu___255_17874.synth_hook);
        splice = (uu___255_17874.splice);
        is_native_tactic = (uu___255_17874.is_native_tactic);
        identifier_info = (uu___255_17874.identifier_info);
        tc_hooks = (uu___255_17874.tc_hooks);
        dsenv = (uu___255_17874.dsenv);
        dep_graph = (uu___255_17874.dep_graph)
      }), uu____17868)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17884 =
      let uu____17887 = FStar_Ident.id_of_text ""  in [uu____17887]  in
    FStar_Ident.lid_of_ids uu____17884  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17893 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17893
        then
          let uu____17896 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17896 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___256_17923 = env  in
       {
         solver = (uu___256_17923.solver);
         range = (uu___256_17923.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___256_17923.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___256_17923.expected_typ);
         sigtab = (uu___256_17923.sigtab);
         is_pattern = (uu___256_17923.is_pattern);
         instantiate_imp = (uu___256_17923.instantiate_imp);
         effects = (uu___256_17923.effects);
         generalize = (uu___256_17923.generalize);
         letrecs = (uu___256_17923.letrecs);
         top_level = (uu___256_17923.top_level);
         check_uvars = (uu___256_17923.check_uvars);
         use_eq = (uu___256_17923.use_eq);
         is_iface = (uu___256_17923.is_iface);
         admit = (uu___256_17923.admit);
         lax = (uu___256_17923.lax);
         lax_universes = (uu___256_17923.lax_universes);
         phase1 = (uu___256_17923.phase1);
         failhard = (uu___256_17923.failhard);
         nosynth = (uu___256_17923.nosynth);
         uvar_subtyping = (uu___256_17923.uvar_subtyping);
         tc_term = (uu___256_17923.tc_term);
         type_of = (uu___256_17923.type_of);
         universe_of = (uu___256_17923.universe_of);
         check_type_of = (uu___256_17923.check_type_of);
         use_bv_sorts = (uu___256_17923.use_bv_sorts);
         qtbl_name_and_index = (uu___256_17923.qtbl_name_and_index);
         normalized_eff_names = (uu___256_17923.normalized_eff_names);
         proof_ns = (uu___256_17923.proof_ns);
         synth_hook = (uu___256_17923.synth_hook);
         splice = (uu___256_17923.splice);
         is_native_tactic = (uu___256_17923.is_native_tactic);
         identifier_info = (uu___256_17923.identifier_info);
         tc_hooks = (uu___256_17923.tc_hooks);
         dsenv = (uu___256_17923.dsenv);
         dep_graph = (uu___256_17923.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17974)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17978,(uu____17979,t)))::tl1
          ->
          let uu____18000 =
            let uu____18003 = FStar_Syntax_Free.uvars t  in
            ext out uu____18003  in
          aux uu____18000 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18006;
            FStar_Syntax_Syntax.index = uu____18007;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18014 =
            let uu____18017 = FStar_Syntax_Free.uvars t  in
            ext out uu____18017  in
          aux uu____18014 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18074)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18078,(uu____18079,t)))::tl1
          ->
          let uu____18100 =
            let uu____18103 = FStar_Syntax_Free.univs t  in
            ext out uu____18103  in
          aux uu____18100 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18106;
            FStar_Syntax_Syntax.index = uu____18107;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18114 =
            let uu____18117 = FStar_Syntax_Free.univs t  in
            ext out uu____18117  in
          aux uu____18114 tl1
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
          let uu____18178 = FStar_Util.set_add uname out  in
          aux uu____18178 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18181,(uu____18182,t)))::tl1
          ->
          let uu____18203 =
            let uu____18206 = FStar_Syntax_Free.univnames t  in
            ext out uu____18206  in
          aux uu____18203 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18209;
            FStar_Syntax_Syntax.index = uu____18210;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18217 =
            let uu____18220 = FStar_Syntax_Free.univnames t  in
            ext out uu____18220  in
          aux uu____18217 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___230_18240  ->
            match uu___230_18240 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18244 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____18257 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____18267 =
      let uu____18274 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____18274
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____18267 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____18312 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___231_18322  ->
              match uu___231_18322 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____18324 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____18324
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____18327) ->
                  let uu____18344 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____18344))
       in
    FStar_All.pipe_right uu____18312 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___232_18351  ->
    match uu___232_18351 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____18353 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____18353
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18373  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18415) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18434,uu____18435) -> false  in
      let uu____18444 =
        FStar_List.tryFind
          (fun uu____18462  ->
             match uu____18462 with | (p,uu____18470) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18444 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18481,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18503 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18503
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___257_18521 = e  in
        {
          solver = (uu___257_18521.solver);
          range = (uu___257_18521.range);
          curmodule = (uu___257_18521.curmodule);
          gamma = (uu___257_18521.gamma);
          gamma_sig = (uu___257_18521.gamma_sig);
          gamma_cache = (uu___257_18521.gamma_cache);
          modules = (uu___257_18521.modules);
          expected_typ = (uu___257_18521.expected_typ);
          sigtab = (uu___257_18521.sigtab);
          is_pattern = (uu___257_18521.is_pattern);
          instantiate_imp = (uu___257_18521.instantiate_imp);
          effects = (uu___257_18521.effects);
          generalize = (uu___257_18521.generalize);
          letrecs = (uu___257_18521.letrecs);
          top_level = (uu___257_18521.top_level);
          check_uvars = (uu___257_18521.check_uvars);
          use_eq = (uu___257_18521.use_eq);
          is_iface = (uu___257_18521.is_iface);
          admit = (uu___257_18521.admit);
          lax = (uu___257_18521.lax);
          lax_universes = (uu___257_18521.lax_universes);
          phase1 = (uu___257_18521.phase1);
          failhard = (uu___257_18521.failhard);
          nosynth = (uu___257_18521.nosynth);
          uvar_subtyping = (uu___257_18521.uvar_subtyping);
          tc_term = (uu___257_18521.tc_term);
          type_of = (uu___257_18521.type_of);
          universe_of = (uu___257_18521.universe_of);
          check_type_of = (uu___257_18521.check_type_of);
          use_bv_sorts = (uu___257_18521.use_bv_sorts);
          qtbl_name_and_index = (uu___257_18521.qtbl_name_and_index);
          normalized_eff_names = (uu___257_18521.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___257_18521.synth_hook);
          splice = (uu___257_18521.splice);
          is_native_tactic = (uu___257_18521.is_native_tactic);
          identifier_info = (uu___257_18521.identifier_info);
          tc_hooks = (uu___257_18521.tc_hooks);
          dsenv = (uu___257_18521.dsenv);
          dep_graph = (uu___257_18521.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___258_18561 = e  in
      {
        solver = (uu___258_18561.solver);
        range = (uu___258_18561.range);
        curmodule = (uu___258_18561.curmodule);
        gamma = (uu___258_18561.gamma);
        gamma_sig = (uu___258_18561.gamma_sig);
        gamma_cache = (uu___258_18561.gamma_cache);
        modules = (uu___258_18561.modules);
        expected_typ = (uu___258_18561.expected_typ);
        sigtab = (uu___258_18561.sigtab);
        is_pattern = (uu___258_18561.is_pattern);
        instantiate_imp = (uu___258_18561.instantiate_imp);
        effects = (uu___258_18561.effects);
        generalize = (uu___258_18561.generalize);
        letrecs = (uu___258_18561.letrecs);
        top_level = (uu___258_18561.top_level);
        check_uvars = (uu___258_18561.check_uvars);
        use_eq = (uu___258_18561.use_eq);
        is_iface = (uu___258_18561.is_iface);
        admit = (uu___258_18561.admit);
        lax = (uu___258_18561.lax);
        lax_universes = (uu___258_18561.lax_universes);
        phase1 = (uu___258_18561.phase1);
        failhard = (uu___258_18561.failhard);
        nosynth = (uu___258_18561.nosynth);
        uvar_subtyping = (uu___258_18561.uvar_subtyping);
        tc_term = (uu___258_18561.tc_term);
        type_of = (uu___258_18561.type_of);
        universe_of = (uu___258_18561.universe_of);
        check_type_of = (uu___258_18561.check_type_of);
        use_bv_sorts = (uu___258_18561.use_bv_sorts);
        qtbl_name_and_index = (uu___258_18561.qtbl_name_and_index);
        normalized_eff_names = (uu___258_18561.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___258_18561.synth_hook);
        splice = (uu___258_18561.splice);
        is_native_tactic = (uu___258_18561.is_native_tactic);
        identifier_info = (uu___258_18561.identifier_info);
        tc_hooks = (uu___258_18561.tc_hooks);
        dsenv = (uu___258_18561.dsenv);
        dep_graph = (uu___258_18561.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18576 = FStar_Syntax_Free.names t  in
      let uu____18579 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18576 uu____18579
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18600 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18600
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18608 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18608
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18625 =
      match uu____18625 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18635 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18635)
       in
    let uu____18637 =
      let uu____18640 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18640 FStar_List.rev  in
    FStar_All.pipe_right uu____18637 (FStar_String.concat " ")
  
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
             (fun uu____18726  ->
                match uu____18726 with
                | (uu____18735,uu____18736,ctx_uvar,uu____18738) ->
                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check =
                       FStar_Syntax_Syntax.Allow_unresolved)
                      ||
                      (let uu____18741 =
                         FStar_Syntax_Unionfind.find
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       (match uu____18741 with
                        | FStar_Pervasives_Native.Some uu____18744 -> true
                        | FStar_Pervasives_Native.None  -> false))))
    | uu____18745 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____18751;
        univ_ineqs = uu____18752; implicits = uu____18753;_} -> true
    | uu____18772 -> false
  
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
          let uu___259_18807 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___259_18807.deferred);
            univ_ineqs = (uu___259_18807.univ_ineqs);
            implicits = (uu___259_18807.implicits)
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
          let uu____18842 = FStar_Options.defensive ()  in
          if uu____18842
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____18846 =
              let uu____18847 =
                let uu____18848 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____18848  in
              Prims.op_Negation uu____18847  in
            (if uu____18846
             then
               let uu____18853 =
                 let uu____18858 =
                   let uu____18859 = FStar_Syntax_Print.term_to_string t  in
                   let uu____18860 =
                     let uu____18861 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____18861
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____18859 uu____18860
                    in
                 (FStar_Errors.Warning_Defensive, uu____18858)  in
               FStar_Errors.log_issue rng uu____18853
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
          let uu____18892 =
            let uu____18893 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____18893  in
          if uu____18892
          then ()
          else
            (let uu____18895 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____18895 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____18918 =
            let uu____18919 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____18919  in
          if uu____18918
          then ()
          else
            (let uu____18921 = bound_vars e  in
             def_check_closed_in rng msg uu____18921 t)
  
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
          let uu___260_18956 = g  in
          let uu____18957 =
            let uu____18958 =
              let uu____18959 =
                let uu____18966 =
                  let uu____18967 =
                    let uu____18982 =
                      let uu____18991 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____18991]  in
                    (f, uu____18982)  in
                  FStar_Syntax_Syntax.Tm_app uu____18967  in
                FStar_Syntax_Syntax.mk uu____18966  in
              uu____18959 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____18958
             in
          {
            guard_f = uu____18957;
            deferred = (uu___260_18956.deferred);
            univ_ineqs = (uu___260_18956.univ_ineqs);
            implicits = (uu___260_18956.implicits)
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
          let uu___261_19039 = g  in
          let uu____19040 =
            let uu____19041 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19041  in
          {
            guard_f = uu____19040;
            deferred = (uu___261_19039.deferred);
            univ_ineqs = (uu___261_19039.univ_ineqs);
            implicits = (uu___261_19039.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19047 ->
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
          let uu____19062 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19062
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19068 =
      let uu____19069 = FStar_Syntax_Util.unmeta t  in
      uu____19069.FStar_Syntax_Syntax.n  in
    match uu____19068 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19073 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____19114 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19114;
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
                       let uu____19199 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____19199
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___262_19201 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___262_19201.deferred);
              univ_ineqs = (uu___262_19201.univ_ineqs);
              implicits = (uu___262_19201.implicits)
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
               let uu____19230 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____19230
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
            let uu___263_19249 = g  in
            let uu____19250 =
              let uu____19251 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____19251  in
            {
              guard_f = uu____19250;
              deferred = (uu___263_19249.deferred);
              univ_ineqs = (uu___263_19249.univ_ineqs);
              implicits = (uu___263_19249.implicits)
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
            let uu____19289 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____19289 with
            | FStar_Pervasives_Native.Some
                (uu____19312::(tm,uu____19314)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____19364 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____19380 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____19380;
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
                    let uu___264_19410 = trivial_guard  in
                    {
                      guard_f = (uu___264_19410.guard_f);
                      deferred = (uu___264_19410.deferred);
                      univ_ineqs = (uu___264_19410.univ_ineqs);
                      implicits = [(reason, t, ctx_uvar, r)]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____19443  -> ());
    push = (fun uu____19445  -> ());
    pop = (fun uu____19447  -> ());
    snapshot =
      (fun uu____19449  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____19458  -> fun uu____19459  -> ());
    encode_modul = (fun uu____19470  -> fun uu____19471  -> ());
    encode_sig = (fun uu____19474  -> fun uu____19475  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____19481 =
             let uu____19488 = FStar_Options.peek ()  in (e, g, uu____19488)
              in
           [uu____19481]);
    solve = (fun uu____19504  -> fun uu____19505  -> fun uu____19506  -> ());
    finish = (fun uu____19512  -> ());
    refresh = (fun uu____19514  -> ())
  } 