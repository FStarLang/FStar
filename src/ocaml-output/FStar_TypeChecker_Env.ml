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
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap ;
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
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        dep_graph = __fname__dep_graph;_} -> __fname__attrtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
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
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;_} ->
        __fname__imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;_} ->
        __fname__imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;_} ->
        __fname__imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;_} ->
        __fname__imp_range
  
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
type implicits = implicit Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___219_8809  ->
              match uu___219_8809 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8812 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8812  in
                  let uu____8813 =
                    let uu____8814 = FStar_Syntax_Subst.compress y  in
                    uu____8814.FStar_Syntax_Syntax.n  in
                  (match uu____8813 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8818 =
                         let uu___233_8819 = y1  in
                         let uu____8820 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___233_8819.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___233_8819.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8820
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8818
                   | uu____8823 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___234_8835 = env  in
      let uu____8836 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___234_8835.solver);
        range = (uu___234_8835.range);
        curmodule = (uu___234_8835.curmodule);
        gamma = uu____8836;
        gamma_sig = (uu___234_8835.gamma_sig);
        gamma_cache = (uu___234_8835.gamma_cache);
        modules = (uu___234_8835.modules);
        expected_typ = (uu___234_8835.expected_typ);
        sigtab = (uu___234_8835.sigtab);
        attrtab = (uu___234_8835.attrtab);
        is_pattern = (uu___234_8835.is_pattern);
        instantiate_imp = (uu___234_8835.instantiate_imp);
        effects = (uu___234_8835.effects);
        generalize = (uu___234_8835.generalize);
        letrecs = (uu___234_8835.letrecs);
        top_level = (uu___234_8835.top_level);
        check_uvars = (uu___234_8835.check_uvars);
        use_eq = (uu___234_8835.use_eq);
        is_iface = (uu___234_8835.is_iface);
        admit = (uu___234_8835.admit);
        lax = (uu___234_8835.lax);
        lax_universes = (uu___234_8835.lax_universes);
        phase1 = (uu___234_8835.phase1);
        failhard = (uu___234_8835.failhard);
        nosynth = (uu___234_8835.nosynth);
        uvar_subtyping = (uu___234_8835.uvar_subtyping);
        tc_term = (uu___234_8835.tc_term);
        type_of = (uu___234_8835.type_of);
        universe_of = (uu___234_8835.universe_of);
        check_type_of = (uu___234_8835.check_type_of);
        use_bv_sorts = (uu___234_8835.use_bv_sorts);
        qtbl_name_and_index = (uu___234_8835.qtbl_name_and_index);
        normalized_eff_names = (uu___234_8835.normalized_eff_names);
        proof_ns = (uu___234_8835.proof_ns);
        synth_hook = (uu___234_8835.synth_hook);
        splice = (uu___234_8835.splice);
        is_native_tactic = (uu___234_8835.is_native_tactic);
        identifier_info = (uu___234_8835.identifier_info);
        tc_hooks = (uu___234_8835.tc_hooks);
        dsenv = (uu___234_8835.dsenv);
        dep_graph = (uu___234_8835.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8843  -> fun uu____8844  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___235_8864 = env  in
      {
        solver = (uu___235_8864.solver);
        range = (uu___235_8864.range);
        curmodule = (uu___235_8864.curmodule);
        gamma = (uu___235_8864.gamma);
        gamma_sig = (uu___235_8864.gamma_sig);
        gamma_cache = (uu___235_8864.gamma_cache);
        modules = (uu___235_8864.modules);
        expected_typ = (uu___235_8864.expected_typ);
        sigtab = (uu___235_8864.sigtab);
        attrtab = (uu___235_8864.attrtab);
        is_pattern = (uu___235_8864.is_pattern);
        instantiate_imp = (uu___235_8864.instantiate_imp);
        effects = (uu___235_8864.effects);
        generalize = (uu___235_8864.generalize);
        letrecs = (uu___235_8864.letrecs);
        top_level = (uu___235_8864.top_level);
        check_uvars = (uu___235_8864.check_uvars);
        use_eq = (uu___235_8864.use_eq);
        is_iface = (uu___235_8864.is_iface);
        admit = (uu___235_8864.admit);
        lax = (uu___235_8864.lax);
        lax_universes = (uu___235_8864.lax_universes);
        phase1 = (uu___235_8864.phase1);
        failhard = (uu___235_8864.failhard);
        nosynth = (uu___235_8864.nosynth);
        uvar_subtyping = (uu___235_8864.uvar_subtyping);
        tc_term = (uu___235_8864.tc_term);
        type_of = (uu___235_8864.type_of);
        universe_of = (uu___235_8864.universe_of);
        check_type_of = (uu___235_8864.check_type_of);
        use_bv_sorts = (uu___235_8864.use_bv_sorts);
        qtbl_name_and_index = (uu___235_8864.qtbl_name_and_index);
        normalized_eff_names = (uu___235_8864.normalized_eff_names);
        proof_ns = (uu___235_8864.proof_ns);
        synth_hook = (uu___235_8864.synth_hook);
        splice = (uu___235_8864.splice);
        is_native_tactic = (uu___235_8864.is_native_tactic);
        identifier_info = (uu___235_8864.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___235_8864.dsenv);
        dep_graph = (uu___235_8864.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___236_8875 = e  in
      {
        solver = (uu___236_8875.solver);
        range = (uu___236_8875.range);
        curmodule = (uu___236_8875.curmodule);
        gamma = (uu___236_8875.gamma);
        gamma_sig = (uu___236_8875.gamma_sig);
        gamma_cache = (uu___236_8875.gamma_cache);
        modules = (uu___236_8875.modules);
        expected_typ = (uu___236_8875.expected_typ);
        sigtab = (uu___236_8875.sigtab);
        attrtab = (uu___236_8875.attrtab);
        is_pattern = (uu___236_8875.is_pattern);
        instantiate_imp = (uu___236_8875.instantiate_imp);
        effects = (uu___236_8875.effects);
        generalize = (uu___236_8875.generalize);
        letrecs = (uu___236_8875.letrecs);
        top_level = (uu___236_8875.top_level);
        check_uvars = (uu___236_8875.check_uvars);
        use_eq = (uu___236_8875.use_eq);
        is_iface = (uu___236_8875.is_iface);
        admit = (uu___236_8875.admit);
        lax = (uu___236_8875.lax);
        lax_universes = (uu___236_8875.lax_universes);
        phase1 = (uu___236_8875.phase1);
        failhard = (uu___236_8875.failhard);
        nosynth = (uu___236_8875.nosynth);
        uvar_subtyping = (uu___236_8875.uvar_subtyping);
        tc_term = (uu___236_8875.tc_term);
        type_of = (uu___236_8875.type_of);
        universe_of = (uu___236_8875.universe_of);
        check_type_of = (uu___236_8875.check_type_of);
        use_bv_sorts = (uu___236_8875.use_bv_sorts);
        qtbl_name_and_index = (uu___236_8875.qtbl_name_and_index);
        normalized_eff_names = (uu___236_8875.normalized_eff_names);
        proof_ns = (uu___236_8875.proof_ns);
        synth_hook = (uu___236_8875.synth_hook);
        splice = (uu___236_8875.splice);
        is_native_tactic = (uu___236_8875.is_native_tactic);
        identifier_info = (uu___236_8875.identifier_info);
        tc_hooks = (uu___236_8875.tc_hooks);
        dsenv = (uu___236_8875.dsenv);
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
      | (NoDelta ,uu____8898) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8899,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8900,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8901 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8910 . unit -> 'Auu____8910 FStar_Util.smap =
  fun uu____8917  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8922 . unit -> 'Auu____8922 FStar_Util.smap =
  fun uu____8929  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____9039 = new_gamma_cache ()  in
                let uu____9042 = new_sigtab ()  in
                let uu____9045 = new_sigtab ()  in
                let uu____9052 =
                  let uu____9065 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____9065, FStar_Pervasives_Native.None)  in
                let uu____9080 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____9083 = FStar_Options.using_facts_from ()  in
                let uu____9084 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____9087 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____9039;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____9042;
                  attrtab = uu____9045;
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
                  qtbl_name_and_index = uu____9052;
                  normalized_eff_names = uu____9080;
                  proof_ns = uu____9083;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____9123  -> false);
                  identifier_info = uu____9084;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____9087;
                  dep_graph = deps
                }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____9223  ->
    let uu____9224 = FStar_ST.op_Bang query_indices  in
    match uu____9224 with
    | [] -> failwith "Empty query indices!"
    | uu____9278 ->
        let uu____9287 =
          let uu____9296 =
            let uu____9303 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____9303  in
          let uu____9357 = FStar_ST.op_Bang query_indices  in uu____9296 ::
            uu____9357
           in
        FStar_ST.op_Colon_Equals query_indices uu____9287
  
let (pop_query_indices : unit -> unit) =
  fun uu____9454  ->
    let uu____9455 = FStar_ST.op_Bang query_indices  in
    match uu____9455 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9578  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9608  ->
    match uu____9608 with
    | (l,n1) ->
        let uu____9615 = FStar_ST.op_Bang query_indices  in
        (match uu____9615 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9734 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9753  ->
    let uu____9754 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9754
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9831 =
       let uu____9834 = FStar_ST.op_Bang stack  in env :: uu____9834  in
     FStar_ST.op_Colon_Equals stack uu____9831);
    (let uu___237_9891 = env  in
     let uu____9892 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9895 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9898 = FStar_Util.smap_copy (attrtab env)  in
     let uu____9905 =
       let uu____9918 =
         let uu____9921 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9921  in
       let uu____9946 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9918, uu____9946)  in
     let uu____9987 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9990 =
       let uu____9993 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9993  in
     {
       solver = (uu___237_9891.solver);
       range = (uu___237_9891.range);
       curmodule = (uu___237_9891.curmodule);
       gamma = (uu___237_9891.gamma);
       gamma_sig = (uu___237_9891.gamma_sig);
       gamma_cache = uu____9892;
       modules = (uu___237_9891.modules);
       expected_typ = (uu___237_9891.expected_typ);
       sigtab = uu____9895;
       attrtab = uu____9898;
       is_pattern = (uu___237_9891.is_pattern);
       instantiate_imp = (uu___237_9891.instantiate_imp);
       effects = (uu___237_9891.effects);
       generalize = (uu___237_9891.generalize);
       letrecs = (uu___237_9891.letrecs);
       top_level = (uu___237_9891.top_level);
       check_uvars = (uu___237_9891.check_uvars);
       use_eq = (uu___237_9891.use_eq);
       is_iface = (uu___237_9891.is_iface);
       admit = (uu___237_9891.admit);
       lax = (uu___237_9891.lax);
       lax_universes = (uu___237_9891.lax_universes);
       phase1 = (uu___237_9891.phase1);
       failhard = (uu___237_9891.failhard);
       nosynth = (uu___237_9891.nosynth);
       uvar_subtyping = (uu___237_9891.uvar_subtyping);
       tc_term = (uu___237_9891.tc_term);
       type_of = (uu___237_9891.type_of);
       universe_of = (uu___237_9891.universe_of);
       check_type_of = (uu___237_9891.check_type_of);
       use_bv_sorts = (uu___237_9891.use_bv_sorts);
       qtbl_name_and_index = uu____9905;
       normalized_eff_names = uu____9987;
       proof_ns = (uu___237_9891.proof_ns);
       synth_hook = (uu___237_9891.synth_hook);
       splice = (uu___237_9891.splice);
       is_native_tactic = (uu___237_9891.is_native_tactic);
       identifier_info = uu____9990;
       tc_hooks = (uu___237_9891.tc_hooks);
       dsenv = (uu___237_9891.dsenv);
       dep_graph = (uu___237_9891.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____10043  ->
    let uu____10044 = FStar_ST.op_Bang stack  in
    match uu____10044 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10106 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____10178  ->
           let uu____10179 = snapshot_stack env  in
           match uu____10179 with
           | (stack_depth,env1) ->
               let uu____10204 = snapshot_query_indices ()  in
               (match uu____10204 with
                | (query_indices_depth,()) ->
                    let uu____10228 = (env1.solver).snapshot msg  in
                    (match uu____10228 with
                     | (solver_depth,()) ->
                         let uu____10270 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____10270 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___238_10316 = env1  in
                                 {
                                   solver = (uu___238_10316.solver);
                                   range = (uu___238_10316.range);
                                   curmodule = (uu___238_10316.curmodule);
                                   gamma = (uu___238_10316.gamma);
                                   gamma_sig = (uu___238_10316.gamma_sig);
                                   gamma_cache = (uu___238_10316.gamma_cache);
                                   modules = (uu___238_10316.modules);
                                   expected_typ =
                                     (uu___238_10316.expected_typ);
                                   sigtab = (uu___238_10316.sigtab);
                                   attrtab = (uu___238_10316.attrtab);
                                   is_pattern = (uu___238_10316.is_pattern);
                                   instantiate_imp =
                                     (uu___238_10316.instantiate_imp);
                                   effects = (uu___238_10316.effects);
                                   generalize = (uu___238_10316.generalize);
                                   letrecs = (uu___238_10316.letrecs);
                                   top_level = (uu___238_10316.top_level);
                                   check_uvars = (uu___238_10316.check_uvars);
                                   use_eq = (uu___238_10316.use_eq);
                                   is_iface = (uu___238_10316.is_iface);
                                   admit = (uu___238_10316.admit);
                                   lax = (uu___238_10316.lax);
                                   lax_universes =
                                     (uu___238_10316.lax_universes);
                                   phase1 = (uu___238_10316.phase1);
                                   failhard = (uu___238_10316.failhard);
                                   nosynth = (uu___238_10316.nosynth);
                                   uvar_subtyping =
                                     (uu___238_10316.uvar_subtyping);
                                   tc_term = (uu___238_10316.tc_term);
                                   type_of = (uu___238_10316.type_of);
                                   universe_of = (uu___238_10316.universe_of);
                                   check_type_of =
                                     (uu___238_10316.check_type_of);
                                   use_bv_sorts =
                                     (uu___238_10316.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___238_10316.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___238_10316.normalized_eff_names);
                                   proof_ns = (uu___238_10316.proof_ns);
                                   synth_hook = (uu___238_10316.synth_hook);
                                   splice = (uu___238_10316.splice);
                                   is_native_tactic =
                                     (uu___238_10316.is_native_tactic);
                                   identifier_info =
                                     (uu___238_10316.identifier_info);
                                   tc_hooks = (uu___238_10316.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___238_10316.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____10347  ->
             let uu____10348 =
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
             match uu____10348 with
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
                             ((let uu____10474 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____10474
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____10485 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____10485
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____10512,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____10544 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10570  ->
                  match uu____10570 with
                  | (m,uu____10576) -> FStar_Ident.lid_equals l m))
           in
        (match uu____10544 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___239_10584 = env  in
               {
                 solver = (uu___239_10584.solver);
                 range = (uu___239_10584.range);
                 curmodule = (uu___239_10584.curmodule);
                 gamma = (uu___239_10584.gamma);
                 gamma_sig = (uu___239_10584.gamma_sig);
                 gamma_cache = (uu___239_10584.gamma_cache);
                 modules = (uu___239_10584.modules);
                 expected_typ = (uu___239_10584.expected_typ);
                 sigtab = (uu___239_10584.sigtab);
                 attrtab = (uu___239_10584.attrtab);
                 is_pattern = (uu___239_10584.is_pattern);
                 instantiate_imp = (uu___239_10584.instantiate_imp);
                 effects = (uu___239_10584.effects);
                 generalize = (uu___239_10584.generalize);
                 letrecs = (uu___239_10584.letrecs);
                 top_level = (uu___239_10584.top_level);
                 check_uvars = (uu___239_10584.check_uvars);
                 use_eq = (uu___239_10584.use_eq);
                 is_iface = (uu___239_10584.is_iface);
                 admit = (uu___239_10584.admit);
                 lax = (uu___239_10584.lax);
                 lax_universes = (uu___239_10584.lax_universes);
                 phase1 = (uu___239_10584.phase1);
                 failhard = (uu___239_10584.failhard);
                 nosynth = (uu___239_10584.nosynth);
                 uvar_subtyping = (uu___239_10584.uvar_subtyping);
                 tc_term = (uu___239_10584.tc_term);
                 type_of = (uu___239_10584.type_of);
                 universe_of = (uu___239_10584.universe_of);
                 check_type_of = (uu___239_10584.check_type_of);
                 use_bv_sorts = (uu___239_10584.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___239_10584.normalized_eff_names);
                 proof_ns = (uu___239_10584.proof_ns);
                 synth_hook = (uu___239_10584.synth_hook);
                 splice = (uu___239_10584.splice);
                 is_native_tactic = (uu___239_10584.is_native_tactic);
                 identifier_info = (uu___239_10584.identifier_info);
                 tc_hooks = (uu___239_10584.tc_hooks);
                 dsenv = (uu___239_10584.dsenv);
                 dep_graph = (uu___239_10584.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____10597,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_10606 = env  in
               {
                 solver = (uu___240_10606.solver);
                 range = (uu___240_10606.range);
                 curmodule = (uu___240_10606.curmodule);
                 gamma = (uu___240_10606.gamma);
                 gamma_sig = (uu___240_10606.gamma_sig);
                 gamma_cache = (uu___240_10606.gamma_cache);
                 modules = (uu___240_10606.modules);
                 expected_typ = (uu___240_10606.expected_typ);
                 sigtab = (uu___240_10606.sigtab);
                 attrtab = (uu___240_10606.attrtab);
                 is_pattern = (uu___240_10606.is_pattern);
                 instantiate_imp = (uu___240_10606.instantiate_imp);
                 effects = (uu___240_10606.effects);
                 generalize = (uu___240_10606.generalize);
                 letrecs = (uu___240_10606.letrecs);
                 top_level = (uu___240_10606.top_level);
                 check_uvars = (uu___240_10606.check_uvars);
                 use_eq = (uu___240_10606.use_eq);
                 is_iface = (uu___240_10606.is_iface);
                 admit = (uu___240_10606.admit);
                 lax = (uu___240_10606.lax);
                 lax_universes = (uu___240_10606.lax_universes);
                 phase1 = (uu___240_10606.phase1);
                 failhard = (uu___240_10606.failhard);
                 nosynth = (uu___240_10606.nosynth);
                 uvar_subtyping = (uu___240_10606.uvar_subtyping);
                 tc_term = (uu___240_10606.tc_term);
                 type_of = (uu___240_10606.type_of);
                 universe_of = (uu___240_10606.universe_of);
                 check_type_of = (uu___240_10606.check_type_of);
                 use_bv_sorts = (uu___240_10606.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_10606.normalized_eff_names);
                 proof_ns = (uu___240_10606.proof_ns);
                 synth_hook = (uu___240_10606.synth_hook);
                 splice = (uu___240_10606.splice);
                 is_native_tactic = (uu___240_10606.is_native_tactic);
                 identifier_info = (uu___240_10606.identifier_info);
                 tc_hooks = (uu___240_10606.tc_hooks);
                 dsenv = (uu___240_10606.dsenv);
                 dep_graph = (uu___240_10606.dep_graph)
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
        (let uu___241_10640 = e  in
         {
           solver = (uu___241_10640.solver);
           range = r;
           curmodule = (uu___241_10640.curmodule);
           gamma = (uu___241_10640.gamma);
           gamma_sig = (uu___241_10640.gamma_sig);
           gamma_cache = (uu___241_10640.gamma_cache);
           modules = (uu___241_10640.modules);
           expected_typ = (uu___241_10640.expected_typ);
           sigtab = (uu___241_10640.sigtab);
           attrtab = (uu___241_10640.attrtab);
           is_pattern = (uu___241_10640.is_pattern);
           instantiate_imp = (uu___241_10640.instantiate_imp);
           effects = (uu___241_10640.effects);
           generalize = (uu___241_10640.generalize);
           letrecs = (uu___241_10640.letrecs);
           top_level = (uu___241_10640.top_level);
           check_uvars = (uu___241_10640.check_uvars);
           use_eq = (uu___241_10640.use_eq);
           is_iface = (uu___241_10640.is_iface);
           admit = (uu___241_10640.admit);
           lax = (uu___241_10640.lax);
           lax_universes = (uu___241_10640.lax_universes);
           phase1 = (uu___241_10640.phase1);
           failhard = (uu___241_10640.failhard);
           nosynth = (uu___241_10640.nosynth);
           uvar_subtyping = (uu___241_10640.uvar_subtyping);
           tc_term = (uu___241_10640.tc_term);
           type_of = (uu___241_10640.type_of);
           universe_of = (uu___241_10640.universe_of);
           check_type_of = (uu___241_10640.check_type_of);
           use_bv_sorts = (uu___241_10640.use_bv_sorts);
           qtbl_name_and_index = (uu___241_10640.qtbl_name_and_index);
           normalized_eff_names = (uu___241_10640.normalized_eff_names);
           proof_ns = (uu___241_10640.proof_ns);
           synth_hook = (uu___241_10640.synth_hook);
           splice = (uu___241_10640.splice);
           is_native_tactic = (uu___241_10640.is_native_tactic);
           identifier_info = (uu___241_10640.identifier_info);
           tc_hooks = (uu___241_10640.tc_hooks);
           dsenv = (uu___241_10640.dsenv);
           dep_graph = (uu___241_10640.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10656 =
        let uu____10657 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10657 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10656
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10719 =
          let uu____10720 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10720 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10719
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10782 =
          let uu____10783 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10783 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10782
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10845 =
        let uu____10846 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10846 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10845
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___242_10915 = env  in
      {
        solver = (uu___242_10915.solver);
        range = (uu___242_10915.range);
        curmodule = lid;
        gamma = (uu___242_10915.gamma);
        gamma_sig = (uu___242_10915.gamma_sig);
        gamma_cache = (uu___242_10915.gamma_cache);
        modules = (uu___242_10915.modules);
        expected_typ = (uu___242_10915.expected_typ);
        sigtab = (uu___242_10915.sigtab);
        attrtab = (uu___242_10915.attrtab);
        is_pattern = (uu___242_10915.is_pattern);
        instantiate_imp = (uu___242_10915.instantiate_imp);
        effects = (uu___242_10915.effects);
        generalize = (uu___242_10915.generalize);
        letrecs = (uu___242_10915.letrecs);
        top_level = (uu___242_10915.top_level);
        check_uvars = (uu___242_10915.check_uvars);
        use_eq = (uu___242_10915.use_eq);
        is_iface = (uu___242_10915.is_iface);
        admit = (uu___242_10915.admit);
        lax = (uu___242_10915.lax);
        lax_universes = (uu___242_10915.lax_universes);
        phase1 = (uu___242_10915.phase1);
        failhard = (uu___242_10915.failhard);
        nosynth = (uu___242_10915.nosynth);
        uvar_subtyping = (uu___242_10915.uvar_subtyping);
        tc_term = (uu___242_10915.tc_term);
        type_of = (uu___242_10915.type_of);
        universe_of = (uu___242_10915.universe_of);
        check_type_of = (uu___242_10915.check_type_of);
        use_bv_sorts = (uu___242_10915.use_bv_sorts);
        qtbl_name_and_index = (uu___242_10915.qtbl_name_and_index);
        normalized_eff_names = (uu___242_10915.normalized_eff_names);
        proof_ns = (uu___242_10915.proof_ns);
        synth_hook = (uu___242_10915.synth_hook);
        splice = (uu___242_10915.splice);
        is_native_tactic = (uu___242_10915.is_native_tactic);
        identifier_info = (uu___242_10915.identifier_info);
        tc_hooks = (uu___242_10915.tc_hooks);
        dsenv = (uu___242_10915.dsenv);
        dep_graph = (uu___242_10915.dep_graph)
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
      let uu____10942 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10942
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10952 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10952)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10962 =
      let uu____10963 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10963  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10962)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10968  ->
    let uu____10969 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10969
  
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
      | ((formals,t),uu____11025) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____11059 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11059)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___220_11075  ->
    match uu___220_11075 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11101  -> new_u_univ ()))
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
      let uu____11120 = inst_tscheme t  in
      match uu____11120 with
      | (us,t1) ->
          let uu____11131 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11131)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11151  ->
          match uu____11151 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11170 =
                         let uu____11171 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____11172 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____11173 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____11174 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11171 uu____11172 uu____11173 uu____11174
                          in
                       failwith uu____11170)
                    else ();
                    (let uu____11176 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____11176))
               | uu____11185 ->
                   let uu____11186 =
                     let uu____11187 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____11187
                      in
                   failwith uu____11186)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____11193 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11199 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11205 -> false
  
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
             | ([],uu____11247) -> Maybe
             | (uu____11254,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____11273 -> No  in
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
          let uu____11364 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____11364 with
          | FStar_Pervasives_Native.None  ->
              let uu____11387 =
                FStar_Util.find_map env.gamma
                  (fun uu___221_11431  ->
                     match uu___221_11431 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11470 = FStar_Ident.lid_equals lid l  in
                         if uu____11470
                         then
                           let uu____11491 =
                             let uu____11510 =
                               let uu____11525 = inst_tscheme t  in
                               FStar_Util.Inl uu____11525  in
                             let uu____11540 = FStar_Ident.range_of_lid l  in
                             (uu____11510, uu____11540)  in
                           FStar_Pervasives_Native.Some uu____11491
                         else FStar_Pervasives_Native.None
                     | uu____11592 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11387
                (fun uu____11630  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___222_11639  ->
                        match uu___222_11639 with
                        | (uu____11642,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11644);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11645;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11646;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11647;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11648;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11668 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11668
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
                                  uu____11716 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11723 -> cache t  in
                            let uu____11724 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11724 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11730 =
                                   let uu____11731 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11731)
                                    in
                                 maybe_cache uu____11730)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11799 = find_in_sigtab env lid  in
         match uu____11799 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____11879 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____11879 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____11921 =
          let uu____11924 = lookup_attr env1 attr  in se1 :: uu____11924  in
        FStar_Util.smap_add (attrtab env1) attr uu____11921  in
      FStar_List.iter
        (fun attr  ->
           let uu____11934 =
             let uu____11935 = FStar_Syntax_Subst.compress attr  in
             uu____11935.FStar_Syntax_Syntax.n  in
           match uu____11934 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____11939 =
                 let uu____11940 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____11940.FStar_Ident.str  in
               add_one1 env se uu____11939
           | uu____11941 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11963) ->
          add_sigelts env ses
      | uu____11972 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
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
            | uu____11987 -> ()))

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
        (fun uu___223_12018  ->
           match uu___223_12018 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12036 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____12097,lb::[]),uu____12099) ->
            let uu____12106 =
              let uu____12115 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____12124 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____12115, uu____12124)  in
            FStar_Pervasives_Native.Some uu____12106
        | FStar_Syntax_Syntax.Sig_let ((uu____12137,lbs),uu____12139) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____12169 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____12181 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____12181
                     then
                       let uu____12192 =
                         let uu____12201 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____12210 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____12201, uu____12210)  in
                       FStar_Pervasives_Native.Some uu____12192
                     else FStar_Pervasives_Native.None)
        | uu____12232 -> FStar_Pervasives_Native.None
  
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
          let uu____12291 =
            let uu____12300 =
              let uu____12305 =
                let uu____12306 =
                  let uu____12309 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____12309
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____12306)  in
              inst_tscheme1 uu____12305  in
            (uu____12300, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12291
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____12331,uu____12332) ->
          let uu____12337 =
            let uu____12346 =
              let uu____12351 =
                let uu____12352 =
                  let uu____12355 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____12355  in
                (us, uu____12352)  in
              inst_tscheme1 uu____12351  in
            (uu____12346, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12337
      | uu____12374 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12462 =
          match uu____12462 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12558,uvs,t,uu____12561,uu____12562,uu____12563);
                      FStar_Syntax_Syntax.sigrng = uu____12564;
                      FStar_Syntax_Syntax.sigquals = uu____12565;
                      FStar_Syntax_Syntax.sigmeta = uu____12566;
                      FStar_Syntax_Syntax.sigattrs = uu____12567;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12588 =
                     let uu____12597 = inst_tscheme1 (uvs, t)  in
                     (uu____12597, rng)  in
                   FStar_Pervasives_Native.Some uu____12588
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12621;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12623;
                      FStar_Syntax_Syntax.sigattrs = uu____12624;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12641 =
                     let uu____12642 = in_cur_mod env l  in uu____12642 = Yes
                      in
                   if uu____12641
                   then
                     let uu____12653 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12653
                      then
                        let uu____12666 =
                          let uu____12675 = inst_tscheme1 (uvs, t)  in
                          (uu____12675, rng)  in
                        FStar_Pervasives_Native.Some uu____12666
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12706 =
                        let uu____12715 = inst_tscheme1 (uvs, t)  in
                        (uu____12715, rng)  in
                      FStar_Pervasives_Native.Some uu____12706)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12740,uu____12741);
                      FStar_Syntax_Syntax.sigrng = uu____12742;
                      FStar_Syntax_Syntax.sigquals = uu____12743;
                      FStar_Syntax_Syntax.sigmeta = uu____12744;
                      FStar_Syntax_Syntax.sigattrs = uu____12745;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12784 =
                          let uu____12793 = inst_tscheme1 (uvs, k)  in
                          (uu____12793, rng)  in
                        FStar_Pervasives_Native.Some uu____12784
                    | uu____12814 ->
                        let uu____12815 =
                          let uu____12824 =
                            let uu____12829 =
                              let uu____12830 =
                                let uu____12833 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12833
                                 in
                              (uvs, uu____12830)  in
                            inst_tscheme1 uu____12829  in
                          (uu____12824, rng)  in
                        FStar_Pervasives_Native.Some uu____12815)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12856,uu____12857);
                      FStar_Syntax_Syntax.sigrng = uu____12858;
                      FStar_Syntax_Syntax.sigquals = uu____12859;
                      FStar_Syntax_Syntax.sigmeta = uu____12860;
                      FStar_Syntax_Syntax.sigattrs = uu____12861;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12901 =
                          let uu____12910 = inst_tscheme_with (uvs, k) us  in
                          (uu____12910, rng)  in
                        FStar_Pervasives_Native.Some uu____12901
                    | uu____12931 ->
                        let uu____12932 =
                          let uu____12941 =
                            let uu____12946 =
                              let uu____12947 =
                                let uu____12950 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12950
                                 in
                              (uvs, uu____12947)  in
                            inst_tscheme_with uu____12946 us  in
                          (uu____12941, rng)  in
                        FStar_Pervasives_Native.Some uu____12932)
               | FStar_Util.Inr se ->
                   let uu____12986 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13007;
                          FStar_Syntax_Syntax.sigrng = uu____13008;
                          FStar_Syntax_Syntax.sigquals = uu____13009;
                          FStar_Syntax_Syntax.sigmeta = uu____13010;
                          FStar_Syntax_Syntax.sigattrs = uu____13011;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13026 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12986
                     (FStar_Util.map_option
                        (fun uu____13074  ->
                           match uu____13074 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____13105 =
          let uu____13116 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____13116 mapper  in
        match uu____13105 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____13190 =
              let uu____13201 =
                let uu____13208 =
                  let uu___243_13211 = t  in
                  let uu____13212 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___243_13211.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____13212;
                    FStar_Syntax_Syntax.vars =
                      (uu___243_13211.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____13208)  in
              (uu____13201, r)  in
            FStar_Pervasives_Native.Some uu____13190
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13259 = lookup_qname env l  in
      match uu____13259 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____13278 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____13330 = try_lookup_bv env bv  in
      match uu____13330 with
      | FStar_Pervasives_Native.None  ->
          let uu____13345 = variable_not_found bv  in
          FStar_Errors.raise_error uu____13345 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____13360 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____13361 =
            let uu____13362 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____13362  in
          (uu____13360, uu____13361)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____13383 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____13383 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____13449 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____13449  in
          let uu____13450 =
            let uu____13459 =
              let uu____13464 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13464)  in
            (uu____13459, r1)  in
          FStar_Pervasives_Native.Some uu____13450
  
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
        let uu____13498 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13498 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13531,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13556 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13556  in
            let uu____13557 =
              let uu____13562 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13562, r1)  in
            FStar_Pervasives_Native.Some uu____13557
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13585 = try_lookup_lid env l  in
      match uu____13585 with
      | FStar_Pervasives_Native.None  ->
          let uu____13612 = name_not_found l  in
          let uu____13617 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13612 uu____13617
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___224_13657  ->
              match uu___224_13657 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13659 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13678 = lookup_qname env lid  in
      match uu____13678 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13687,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13690;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13692;
              FStar_Syntax_Syntax.sigattrs = uu____13693;_},FStar_Pervasives_Native.None
            ),uu____13694)
          ->
          let uu____13743 =
            let uu____13750 =
              let uu____13751 =
                let uu____13754 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13754 t  in
              (uvs, uu____13751)  in
            (uu____13750, q)  in
          FStar_Pervasives_Native.Some uu____13743
      | uu____13767 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13788 = lookup_qname env lid  in
      match uu____13788 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13793,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13796;
              FStar_Syntax_Syntax.sigquals = uu____13797;
              FStar_Syntax_Syntax.sigmeta = uu____13798;
              FStar_Syntax_Syntax.sigattrs = uu____13799;_},FStar_Pervasives_Native.None
            ),uu____13800)
          ->
          let uu____13849 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13849 (uvs, t)
      | uu____13854 ->
          let uu____13855 = name_not_found lid  in
          let uu____13860 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13855 uu____13860
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13879 = lookup_qname env lid  in
      match uu____13879 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13884,uvs,t,uu____13887,uu____13888,uu____13889);
              FStar_Syntax_Syntax.sigrng = uu____13890;
              FStar_Syntax_Syntax.sigquals = uu____13891;
              FStar_Syntax_Syntax.sigmeta = uu____13892;
              FStar_Syntax_Syntax.sigattrs = uu____13893;_},FStar_Pervasives_Native.None
            ),uu____13894)
          ->
          let uu____13947 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13947 (uvs, t)
      | uu____13952 ->
          let uu____13953 = name_not_found lid  in
          let uu____13958 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13953 uu____13958
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13979 = lookup_qname env lid  in
      match uu____13979 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13986,uu____13987,uu____13988,uu____13989,uu____13990,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13992;
              FStar_Syntax_Syntax.sigquals = uu____13993;
              FStar_Syntax_Syntax.sigmeta = uu____13994;
              FStar_Syntax_Syntax.sigattrs = uu____13995;_},uu____13996),uu____13997)
          -> (true, dcs)
      | uu____14058 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____14071 = lookup_qname env lid  in
      match uu____14071 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14072,uu____14073,uu____14074,l,uu____14076,uu____14077);
              FStar_Syntax_Syntax.sigrng = uu____14078;
              FStar_Syntax_Syntax.sigquals = uu____14079;
              FStar_Syntax_Syntax.sigmeta = uu____14080;
              FStar_Syntax_Syntax.sigattrs = uu____14081;_},uu____14082),uu____14083)
          -> l
      | uu____14138 ->
          let uu____14139 =
            let uu____14140 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____14140  in
          failwith uu____14139
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14189)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____14240,lbs),uu____14242)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____14264 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____14264
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____14296 -> FStar_Pervasives_Native.None)
        | uu____14301 -> FStar_Pervasives_Native.None
  
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
        let uu____14331 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____14331
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14356),uu____14357) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____14406 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14427 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____14427
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____14446 = lookup_qname env ftv  in
      match uu____14446 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14450) ->
          let uu____14495 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14495 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14516,t),r) ->
               let uu____14531 =
                 let uu____14532 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14532 t  in
               FStar_Pervasives_Native.Some uu____14531)
      | uu____14533 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14544 = try_lookup_effect_lid env ftv  in
      match uu____14544 with
      | FStar_Pervasives_Native.None  ->
          let uu____14547 = name_not_found ftv  in
          let uu____14552 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14547 uu____14552
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
        let uu____14575 = lookup_qname env lid0  in
        match uu____14575 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14586);
                FStar_Syntax_Syntax.sigrng = uu____14587;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14589;
                FStar_Syntax_Syntax.sigattrs = uu____14590;_},FStar_Pervasives_Native.None
              ),uu____14591)
            ->
            let lid1 =
              let uu____14645 =
                let uu____14646 = FStar_Ident.range_of_lid lid  in
                let uu____14647 =
                  let uu____14648 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14648  in
                FStar_Range.set_use_range uu____14646 uu____14647  in
              FStar_Ident.set_lid_range lid uu____14645  in
            let uu____14649 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___225_14653  ->
                      match uu___225_14653 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14654 -> false))
               in
            if uu____14649
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14668 =
                      let uu____14669 =
                        let uu____14670 = get_range env  in
                        FStar_Range.string_of_range uu____14670  in
                      let uu____14671 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14672 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14669 uu____14671 uu____14672
                       in
                    failwith uu____14668)
                  in
               match (binders, univs1) with
               | ([],uu____14687) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14708,uu____14709::uu____14710::uu____14711) ->
                   let uu____14728 =
                     let uu____14729 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14730 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14729 uu____14730
                      in
                   failwith uu____14728
               | uu____14737 ->
                   let uu____14750 =
                     let uu____14755 =
                       let uu____14756 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14756)  in
                     inst_tscheme_with uu____14755 insts  in
                   (match uu____14750 with
                    | (uu____14769,t) ->
                        let t1 =
                          let uu____14772 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14772 t  in
                        let uu____14773 =
                          let uu____14774 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14774.FStar_Syntax_Syntax.n  in
                        (match uu____14773 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14805 -> failwith "Impossible")))
        | uu____14812 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14835 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14835 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14848,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14855 = find1 l2  in
            (match uu____14855 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14862 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14862 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14866 = find1 l  in
            (match uu____14866 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14871 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14871
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14885 = lookup_qname env l1  in
      match uu____14885 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14888;
              FStar_Syntax_Syntax.sigrng = uu____14889;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14891;
              FStar_Syntax_Syntax.sigattrs = uu____14892;_},uu____14893),uu____14894)
          -> q
      | uu____14945 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14966 =
          let uu____14967 =
            let uu____14968 = FStar_Util.string_of_int i  in
            let uu____14969 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14968 uu____14969
             in
          failwith uu____14967  in
        let uu____14970 = lookup_datacon env lid  in
        match uu____14970 with
        | (uu____14975,t) ->
            let uu____14977 =
              let uu____14978 = FStar_Syntax_Subst.compress t  in
              uu____14978.FStar_Syntax_Syntax.n  in
            (match uu____14977 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14982) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____15013 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____15013
                      FStar_Pervasives_Native.fst)
             | uu____15022 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15033 = lookup_qname env l  in
      match uu____15033 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15034,uu____15035,uu____15036);
              FStar_Syntax_Syntax.sigrng = uu____15037;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15039;
              FStar_Syntax_Syntax.sigattrs = uu____15040;_},uu____15041),uu____15042)
          ->
          FStar_Util.for_some
            (fun uu___226_15095  ->
               match uu___226_15095 with
               | FStar_Syntax_Syntax.Projector uu____15096 -> true
               | uu____15101 -> false) quals
      | uu____15102 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15113 = lookup_qname env lid  in
      match uu____15113 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15114,uu____15115,uu____15116,uu____15117,uu____15118,uu____15119);
              FStar_Syntax_Syntax.sigrng = uu____15120;
              FStar_Syntax_Syntax.sigquals = uu____15121;
              FStar_Syntax_Syntax.sigmeta = uu____15122;
              FStar_Syntax_Syntax.sigattrs = uu____15123;_},uu____15124),uu____15125)
          -> true
      | uu____15180 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15191 = lookup_qname env lid  in
      match uu____15191 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15192,uu____15193,uu____15194,uu____15195,uu____15196,uu____15197);
              FStar_Syntax_Syntax.sigrng = uu____15198;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15200;
              FStar_Syntax_Syntax.sigattrs = uu____15201;_},uu____15202),uu____15203)
          ->
          FStar_Util.for_some
            (fun uu___227_15264  ->
               match uu___227_15264 with
               | FStar_Syntax_Syntax.RecordType uu____15265 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____15274 -> true
               | uu____15283 -> false) quals
      | uu____15284 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____15290,uu____15291);
            FStar_Syntax_Syntax.sigrng = uu____15292;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____15294;
            FStar_Syntax_Syntax.sigattrs = uu____15295;_},uu____15296),uu____15297)
        ->
        FStar_Util.for_some
          (fun uu___228_15354  ->
             match uu___228_15354 with
             | FStar_Syntax_Syntax.Action uu____15355 -> true
             | uu____15356 -> false) quals
    | uu____15357 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15368 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____15368
  
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
      let uu____15382 =
        let uu____15383 = FStar_Syntax_Util.un_uinst head1  in
        uu____15383.FStar_Syntax_Syntax.n  in
      match uu____15382 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____15387 ->
               true
           | uu____15388 -> false)
      | uu____15389 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15400 = lookup_qname env l  in
      match uu____15400 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____15402),uu____15403) ->
          FStar_Util.for_some
            (fun uu___229_15451  ->
               match uu___229_15451 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____15452 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____15453 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15524 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15540) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15557 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15564 ->
                 FStar_Pervasives_Native.Some true
             | uu____15581 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15582 =
        let uu____15585 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15585 mapper  in
      match uu____15582 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15635 = lookup_qname env lid  in
      match uu____15635 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15636,uu____15637,tps,uu____15639,uu____15640,uu____15641);
              FStar_Syntax_Syntax.sigrng = uu____15642;
              FStar_Syntax_Syntax.sigquals = uu____15643;
              FStar_Syntax_Syntax.sigmeta = uu____15644;
              FStar_Syntax_Syntax.sigattrs = uu____15645;_},uu____15646),uu____15647)
          -> FStar_List.length tps
      | uu____15710 ->
          let uu____15711 = name_not_found lid  in
          let uu____15716 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15711 uu____15716
  
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
           (fun uu____15760  ->
              match uu____15760 with
              | (d,uu____15768) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15783 = effect_decl_opt env l  in
      match uu____15783 with
      | FStar_Pervasives_Native.None  ->
          let uu____15798 = name_not_found l  in
          let uu____15803 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15798 uu____15803
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15825  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15844  ->
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
        let uu____15875 = FStar_Ident.lid_equals l1 l2  in
        if uu____15875
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15883 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15883
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15891 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15944  ->
                        match uu____15944 with
                        | (m1,m2,uu____15957,uu____15958,uu____15959) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15891 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15976 =
                    let uu____15981 =
                      let uu____15982 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15983 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15982
                        uu____15983
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15981)
                     in
                  FStar_Errors.raise_error uu____15976 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15990,uu____15991,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____16024 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____16024
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
  'Auu____16040 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____16040)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____16069 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____16095  ->
                match uu____16095 with
                | (d,uu____16101) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____16069 with
      | FStar_Pervasives_Native.None  ->
          let uu____16112 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____16112
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____16125 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____16125 with
           | (uu____16140,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____16156)::(wp,uu____16158)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____16194 -> failwith "Impossible"))
  
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
          let uu____16247 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____16247
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____16249 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____16249
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
                  let uu____16257 = get_range env  in
                  let uu____16258 =
                    let uu____16265 =
                      let uu____16266 =
                        let uu____16281 =
                          let uu____16290 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____16290]  in
                        (null_wp, uu____16281)  in
                      FStar_Syntax_Syntax.Tm_app uu____16266  in
                    FStar_Syntax_Syntax.mk uu____16265  in
                  uu____16258 FStar_Pervasives_Native.None uu____16257  in
                let uu____16322 =
                  let uu____16323 =
                    let uu____16332 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____16332]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____16323;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____16322))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___244_16363 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___244_16363.order);
              joins = (uu___244_16363.joins)
            }  in
          let uu___245_16372 = env  in
          {
            solver = (uu___245_16372.solver);
            range = (uu___245_16372.range);
            curmodule = (uu___245_16372.curmodule);
            gamma = (uu___245_16372.gamma);
            gamma_sig = (uu___245_16372.gamma_sig);
            gamma_cache = (uu___245_16372.gamma_cache);
            modules = (uu___245_16372.modules);
            expected_typ = (uu___245_16372.expected_typ);
            sigtab = (uu___245_16372.sigtab);
            attrtab = (uu___245_16372.attrtab);
            is_pattern = (uu___245_16372.is_pattern);
            instantiate_imp = (uu___245_16372.instantiate_imp);
            effects;
            generalize = (uu___245_16372.generalize);
            letrecs = (uu___245_16372.letrecs);
            top_level = (uu___245_16372.top_level);
            check_uvars = (uu___245_16372.check_uvars);
            use_eq = (uu___245_16372.use_eq);
            is_iface = (uu___245_16372.is_iface);
            admit = (uu___245_16372.admit);
            lax = (uu___245_16372.lax);
            lax_universes = (uu___245_16372.lax_universes);
            phase1 = (uu___245_16372.phase1);
            failhard = (uu___245_16372.failhard);
            nosynth = (uu___245_16372.nosynth);
            uvar_subtyping = (uu___245_16372.uvar_subtyping);
            tc_term = (uu___245_16372.tc_term);
            type_of = (uu___245_16372.type_of);
            universe_of = (uu___245_16372.universe_of);
            check_type_of = (uu___245_16372.check_type_of);
            use_bv_sorts = (uu___245_16372.use_bv_sorts);
            qtbl_name_and_index = (uu___245_16372.qtbl_name_and_index);
            normalized_eff_names = (uu___245_16372.normalized_eff_names);
            proof_ns = (uu___245_16372.proof_ns);
            synth_hook = (uu___245_16372.synth_hook);
            splice = (uu___245_16372.splice);
            is_native_tactic = (uu___245_16372.is_native_tactic);
            identifier_info = (uu___245_16372.identifier_info);
            tc_hooks = (uu___245_16372.tc_hooks);
            dsenv = (uu___245_16372.dsenv);
            dep_graph = (uu___245_16372.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____16402 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____16402  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16560 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16561 = l1 u t wp e  in
                                l2 u t uu____16560 uu____16561))
                | uu____16562 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16634 = inst_tscheme_with lift_t [u]  in
            match uu____16634 with
            | (uu____16641,lift_t1) ->
                let uu____16643 =
                  let uu____16650 =
                    let uu____16651 =
                      let uu____16666 =
                        let uu____16675 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16682 =
                          let uu____16691 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16691]  in
                        uu____16675 :: uu____16682  in
                      (lift_t1, uu____16666)  in
                    FStar_Syntax_Syntax.Tm_app uu____16651  in
                  FStar_Syntax_Syntax.mk uu____16650  in
                uu____16643 FStar_Pervasives_Native.None
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
            let uu____16793 = inst_tscheme_with lift_t [u]  in
            match uu____16793 with
            | (uu____16800,lift_t1) ->
                let uu____16802 =
                  let uu____16809 =
                    let uu____16810 =
                      let uu____16825 =
                        let uu____16834 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16841 =
                          let uu____16850 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16857 =
                            let uu____16866 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16866]  in
                          uu____16850 :: uu____16857  in
                        uu____16834 :: uu____16841  in
                      (lift_t1, uu____16825)  in
                    FStar_Syntax_Syntax.Tm_app uu____16810  in
                  FStar_Syntax_Syntax.mk uu____16809  in
                uu____16802 FStar_Pervasives_Native.None
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
              let uu____16956 =
                let uu____16957 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16957
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16956  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16961 =
              let uu____16962 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16962  in
            let uu____16963 =
              let uu____16964 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16990 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16990)
                 in
              FStar_Util.dflt "none" uu____16964  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16961
              uu____16963
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____17016  ->
                    match uu____17016 with
                    | (e,uu____17024) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____17047 =
            match uu____17047 with
            | (i,j) ->
                let uu____17058 = FStar_Ident.lid_equals i j  in
                if uu____17058
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
              let uu____17090 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____17100 = FStar_Ident.lid_equals i k  in
                        if uu____17100
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____17111 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____17111
                                  then []
                                  else
                                    (let uu____17115 =
                                       let uu____17124 =
                                         find_edge order1 (i, k)  in
                                       let uu____17127 =
                                         find_edge order1 (k, j)  in
                                       (uu____17124, uu____17127)  in
                                     match uu____17115 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____17142 =
                                           compose_edges e1 e2  in
                                         [uu____17142]
                                     | uu____17143 -> [])))))
                 in
              FStar_List.append order1 uu____17090  in
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
                   let uu____17173 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____17175 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____17175
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____17173
                   then
                     let uu____17180 =
                       let uu____17185 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____17185)
                        in
                     let uu____17186 = get_range env  in
                     FStar_Errors.raise_error uu____17180 uu____17186
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____17263 = FStar_Ident.lid_equals i j
                                   in
                                if uu____17263
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____17312 =
                                              let uu____17321 =
                                                find_edge order2 (i, k)  in
                                              let uu____17324 =
                                                find_edge order2 (j, k)  in
                                              (uu____17321, uu____17324)  in
                                            match uu____17312 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____17366,uu____17367)
                                                     ->
                                                     let uu____17374 =
                                                       let uu____17379 =
                                                         let uu____17380 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17380
                                                          in
                                                       let uu____17383 =
                                                         let uu____17384 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17384
                                                          in
                                                       (uu____17379,
                                                         uu____17383)
                                                        in
                                                     (match uu____17374 with
                                                      | (true ,true ) ->
                                                          let uu____17395 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____17395
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
                                            | uu____17420 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___246_17493 = env.effects  in
              { decls = (uu___246_17493.decls); order = order2; joins }  in
            let uu___247_17494 = env  in
            {
              solver = (uu___247_17494.solver);
              range = (uu___247_17494.range);
              curmodule = (uu___247_17494.curmodule);
              gamma = (uu___247_17494.gamma);
              gamma_sig = (uu___247_17494.gamma_sig);
              gamma_cache = (uu___247_17494.gamma_cache);
              modules = (uu___247_17494.modules);
              expected_typ = (uu___247_17494.expected_typ);
              sigtab = (uu___247_17494.sigtab);
              attrtab = (uu___247_17494.attrtab);
              is_pattern = (uu___247_17494.is_pattern);
              instantiate_imp = (uu___247_17494.instantiate_imp);
              effects;
              generalize = (uu___247_17494.generalize);
              letrecs = (uu___247_17494.letrecs);
              top_level = (uu___247_17494.top_level);
              check_uvars = (uu___247_17494.check_uvars);
              use_eq = (uu___247_17494.use_eq);
              is_iface = (uu___247_17494.is_iface);
              admit = (uu___247_17494.admit);
              lax = (uu___247_17494.lax);
              lax_universes = (uu___247_17494.lax_universes);
              phase1 = (uu___247_17494.phase1);
              failhard = (uu___247_17494.failhard);
              nosynth = (uu___247_17494.nosynth);
              uvar_subtyping = (uu___247_17494.uvar_subtyping);
              tc_term = (uu___247_17494.tc_term);
              type_of = (uu___247_17494.type_of);
              universe_of = (uu___247_17494.universe_of);
              check_type_of = (uu___247_17494.check_type_of);
              use_bv_sorts = (uu___247_17494.use_bv_sorts);
              qtbl_name_and_index = (uu___247_17494.qtbl_name_and_index);
              normalized_eff_names = (uu___247_17494.normalized_eff_names);
              proof_ns = (uu___247_17494.proof_ns);
              synth_hook = (uu___247_17494.synth_hook);
              splice = (uu___247_17494.splice);
              is_native_tactic = (uu___247_17494.is_native_tactic);
              identifier_info = (uu___247_17494.identifier_info);
              tc_hooks = (uu___247_17494.tc_hooks);
              dsenv = (uu___247_17494.dsenv);
              dep_graph = (uu___247_17494.dep_graph)
            }))
      | uu____17495 -> env
  
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
        | uu____17523 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17535 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17535 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17552 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17552 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17570 =
                     let uu____17575 =
                       let uu____17576 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17581 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17588 =
                         let uu____17589 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17589  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17576 uu____17581 uu____17588
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17575)
                      in
                   FStar_Errors.raise_error uu____17570
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17594 =
                     let uu____17603 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17603 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17632  ->
                        fun uu____17633  ->
                          match (uu____17632, uu____17633) with
                          | ((x,uu____17655),(t,uu____17657)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17594
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____17676 =
                     let uu___248_17677 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___248_17677.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___248_17677.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___248_17677.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___248_17677.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____17676
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
          let uu____17707 = effect_decl_opt env effect_name  in
          match uu____17707 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17740 =
                only_reifiable &&
                  (let uu____17742 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17742)
                 in
              if uu____17740
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17758 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____17777 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____17806 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____17806
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____17807 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____17807
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____17819 =
                       let uu____17822 = get_range env  in
                       let uu____17823 =
                         let uu____17830 =
                           let uu____17831 =
                             let uu____17846 =
                               let uu____17855 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17855; wp]  in
                             (repr, uu____17846)  in
                           FStar_Syntax_Syntax.Tm_app uu____17831  in
                         FStar_Syntax_Syntax.mk uu____17830  in
                       uu____17823 FStar_Pervasives_Native.None uu____17822
                        in
                     FStar_Pervasives_Native.Some uu____17819)
  
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
          let uu____17935 =
            let uu____17940 =
              let uu____17941 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17941
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17940)  in
          let uu____17942 = get_range env  in
          FStar_Errors.raise_error uu____17935 uu____17942  in
        let uu____17943 = effect_repr_aux true env c u_c  in
        match uu____17943 with
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
      | uu____17989 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____18000 =
        let uu____18001 = FStar_Syntax_Subst.compress t  in
        uu____18001.FStar_Syntax_Syntax.n  in
      match uu____18000 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____18004,c) ->
          is_reifiable_comp env c
      | uu____18022 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___249_18043 = env  in
        {
          solver = (uu___249_18043.solver);
          range = (uu___249_18043.range);
          curmodule = (uu___249_18043.curmodule);
          gamma = (uu___249_18043.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___249_18043.gamma_cache);
          modules = (uu___249_18043.modules);
          expected_typ = (uu___249_18043.expected_typ);
          sigtab = (uu___249_18043.sigtab);
          attrtab = (uu___249_18043.attrtab);
          is_pattern = (uu___249_18043.is_pattern);
          instantiate_imp = (uu___249_18043.instantiate_imp);
          effects = (uu___249_18043.effects);
          generalize = (uu___249_18043.generalize);
          letrecs = (uu___249_18043.letrecs);
          top_level = (uu___249_18043.top_level);
          check_uvars = (uu___249_18043.check_uvars);
          use_eq = (uu___249_18043.use_eq);
          is_iface = (uu___249_18043.is_iface);
          admit = (uu___249_18043.admit);
          lax = (uu___249_18043.lax);
          lax_universes = (uu___249_18043.lax_universes);
          phase1 = (uu___249_18043.phase1);
          failhard = (uu___249_18043.failhard);
          nosynth = (uu___249_18043.nosynth);
          uvar_subtyping = (uu___249_18043.uvar_subtyping);
          tc_term = (uu___249_18043.tc_term);
          type_of = (uu___249_18043.type_of);
          universe_of = (uu___249_18043.universe_of);
          check_type_of = (uu___249_18043.check_type_of);
          use_bv_sorts = (uu___249_18043.use_bv_sorts);
          qtbl_name_and_index = (uu___249_18043.qtbl_name_and_index);
          normalized_eff_names = (uu___249_18043.normalized_eff_names);
          proof_ns = (uu___249_18043.proof_ns);
          synth_hook = (uu___249_18043.synth_hook);
          splice = (uu___249_18043.splice);
          is_native_tactic = (uu___249_18043.is_native_tactic);
          identifier_info = (uu___249_18043.identifier_info);
          tc_hooks = (uu___249_18043.tc_hooks);
          dsenv = (uu___249_18043.dsenv);
          dep_graph = (uu___249_18043.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___250_18055 = env  in
      {
        solver = (uu___250_18055.solver);
        range = (uu___250_18055.range);
        curmodule = (uu___250_18055.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___250_18055.gamma_sig);
        gamma_cache = (uu___250_18055.gamma_cache);
        modules = (uu___250_18055.modules);
        expected_typ = (uu___250_18055.expected_typ);
        sigtab = (uu___250_18055.sigtab);
        attrtab = (uu___250_18055.attrtab);
        is_pattern = (uu___250_18055.is_pattern);
        instantiate_imp = (uu___250_18055.instantiate_imp);
        effects = (uu___250_18055.effects);
        generalize = (uu___250_18055.generalize);
        letrecs = (uu___250_18055.letrecs);
        top_level = (uu___250_18055.top_level);
        check_uvars = (uu___250_18055.check_uvars);
        use_eq = (uu___250_18055.use_eq);
        is_iface = (uu___250_18055.is_iface);
        admit = (uu___250_18055.admit);
        lax = (uu___250_18055.lax);
        lax_universes = (uu___250_18055.lax_universes);
        phase1 = (uu___250_18055.phase1);
        failhard = (uu___250_18055.failhard);
        nosynth = (uu___250_18055.nosynth);
        uvar_subtyping = (uu___250_18055.uvar_subtyping);
        tc_term = (uu___250_18055.tc_term);
        type_of = (uu___250_18055.type_of);
        universe_of = (uu___250_18055.universe_of);
        check_type_of = (uu___250_18055.check_type_of);
        use_bv_sorts = (uu___250_18055.use_bv_sorts);
        qtbl_name_and_index = (uu___250_18055.qtbl_name_and_index);
        normalized_eff_names = (uu___250_18055.normalized_eff_names);
        proof_ns = (uu___250_18055.proof_ns);
        synth_hook = (uu___250_18055.synth_hook);
        splice = (uu___250_18055.splice);
        is_native_tactic = (uu___250_18055.is_native_tactic);
        identifier_info = (uu___250_18055.identifier_info);
        tc_hooks = (uu___250_18055.tc_hooks);
        dsenv = (uu___250_18055.dsenv);
        dep_graph = (uu___250_18055.dep_graph)
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
            (let uu___251_18110 = env  in
             {
               solver = (uu___251_18110.solver);
               range = (uu___251_18110.range);
               curmodule = (uu___251_18110.curmodule);
               gamma = rest;
               gamma_sig = (uu___251_18110.gamma_sig);
               gamma_cache = (uu___251_18110.gamma_cache);
               modules = (uu___251_18110.modules);
               expected_typ = (uu___251_18110.expected_typ);
               sigtab = (uu___251_18110.sigtab);
               attrtab = (uu___251_18110.attrtab);
               is_pattern = (uu___251_18110.is_pattern);
               instantiate_imp = (uu___251_18110.instantiate_imp);
               effects = (uu___251_18110.effects);
               generalize = (uu___251_18110.generalize);
               letrecs = (uu___251_18110.letrecs);
               top_level = (uu___251_18110.top_level);
               check_uvars = (uu___251_18110.check_uvars);
               use_eq = (uu___251_18110.use_eq);
               is_iface = (uu___251_18110.is_iface);
               admit = (uu___251_18110.admit);
               lax = (uu___251_18110.lax);
               lax_universes = (uu___251_18110.lax_universes);
               phase1 = (uu___251_18110.phase1);
               failhard = (uu___251_18110.failhard);
               nosynth = (uu___251_18110.nosynth);
               uvar_subtyping = (uu___251_18110.uvar_subtyping);
               tc_term = (uu___251_18110.tc_term);
               type_of = (uu___251_18110.type_of);
               universe_of = (uu___251_18110.universe_of);
               check_type_of = (uu___251_18110.check_type_of);
               use_bv_sorts = (uu___251_18110.use_bv_sorts);
               qtbl_name_and_index = (uu___251_18110.qtbl_name_and_index);
               normalized_eff_names = (uu___251_18110.normalized_eff_names);
               proof_ns = (uu___251_18110.proof_ns);
               synth_hook = (uu___251_18110.synth_hook);
               splice = (uu___251_18110.splice);
               is_native_tactic = (uu___251_18110.is_native_tactic);
               identifier_info = (uu___251_18110.identifier_info);
               tc_hooks = (uu___251_18110.tc_hooks);
               dsenv = (uu___251_18110.dsenv);
               dep_graph = (uu___251_18110.dep_graph)
             }))
    | uu____18111 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____18137  ->
             match uu____18137 with | (x,uu____18143) -> push_bv env1 x) env
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
            let uu___252_18173 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___252_18173.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___252_18173.FStar_Syntax_Syntax.index);
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
      (let uu___253_18213 = env  in
       {
         solver = (uu___253_18213.solver);
         range = (uu___253_18213.range);
         curmodule = (uu___253_18213.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___253_18213.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___253_18213.sigtab);
         attrtab = (uu___253_18213.attrtab);
         is_pattern = (uu___253_18213.is_pattern);
         instantiate_imp = (uu___253_18213.instantiate_imp);
         effects = (uu___253_18213.effects);
         generalize = (uu___253_18213.generalize);
         letrecs = (uu___253_18213.letrecs);
         top_level = (uu___253_18213.top_level);
         check_uvars = (uu___253_18213.check_uvars);
         use_eq = (uu___253_18213.use_eq);
         is_iface = (uu___253_18213.is_iface);
         admit = (uu___253_18213.admit);
         lax = (uu___253_18213.lax);
         lax_universes = (uu___253_18213.lax_universes);
         phase1 = (uu___253_18213.phase1);
         failhard = (uu___253_18213.failhard);
         nosynth = (uu___253_18213.nosynth);
         uvar_subtyping = (uu___253_18213.uvar_subtyping);
         tc_term = (uu___253_18213.tc_term);
         type_of = (uu___253_18213.type_of);
         universe_of = (uu___253_18213.universe_of);
         check_type_of = (uu___253_18213.check_type_of);
         use_bv_sorts = (uu___253_18213.use_bv_sorts);
         qtbl_name_and_index = (uu___253_18213.qtbl_name_and_index);
         normalized_eff_names = (uu___253_18213.normalized_eff_names);
         proof_ns = (uu___253_18213.proof_ns);
         synth_hook = (uu___253_18213.synth_hook);
         splice = (uu___253_18213.splice);
         is_native_tactic = (uu___253_18213.is_native_tactic);
         identifier_info = (uu___253_18213.identifier_info);
         tc_hooks = (uu___253_18213.tc_hooks);
         dsenv = (uu___253_18213.dsenv);
         dep_graph = (uu___253_18213.dep_graph)
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
        let uu____18255 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____18255 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____18283 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____18283)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___254_18298 = env  in
      {
        solver = (uu___254_18298.solver);
        range = (uu___254_18298.range);
        curmodule = (uu___254_18298.curmodule);
        gamma = (uu___254_18298.gamma);
        gamma_sig = (uu___254_18298.gamma_sig);
        gamma_cache = (uu___254_18298.gamma_cache);
        modules = (uu___254_18298.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___254_18298.sigtab);
        attrtab = (uu___254_18298.attrtab);
        is_pattern = (uu___254_18298.is_pattern);
        instantiate_imp = (uu___254_18298.instantiate_imp);
        effects = (uu___254_18298.effects);
        generalize = (uu___254_18298.generalize);
        letrecs = (uu___254_18298.letrecs);
        top_level = (uu___254_18298.top_level);
        check_uvars = (uu___254_18298.check_uvars);
        use_eq = false;
        is_iface = (uu___254_18298.is_iface);
        admit = (uu___254_18298.admit);
        lax = (uu___254_18298.lax);
        lax_universes = (uu___254_18298.lax_universes);
        phase1 = (uu___254_18298.phase1);
        failhard = (uu___254_18298.failhard);
        nosynth = (uu___254_18298.nosynth);
        uvar_subtyping = (uu___254_18298.uvar_subtyping);
        tc_term = (uu___254_18298.tc_term);
        type_of = (uu___254_18298.type_of);
        universe_of = (uu___254_18298.universe_of);
        check_type_of = (uu___254_18298.check_type_of);
        use_bv_sorts = (uu___254_18298.use_bv_sorts);
        qtbl_name_and_index = (uu___254_18298.qtbl_name_and_index);
        normalized_eff_names = (uu___254_18298.normalized_eff_names);
        proof_ns = (uu___254_18298.proof_ns);
        synth_hook = (uu___254_18298.synth_hook);
        splice = (uu___254_18298.splice);
        is_native_tactic = (uu___254_18298.is_native_tactic);
        identifier_info = (uu___254_18298.identifier_info);
        tc_hooks = (uu___254_18298.tc_hooks);
        dsenv = (uu___254_18298.dsenv);
        dep_graph = (uu___254_18298.dep_graph)
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
    let uu____18326 = expected_typ env_  in
    ((let uu___255_18332 = env_  in
      {
        solver = (uu___255_18332.solver);
        range = (uu___255_18332.range);
        curmodule = (uu___255_18332.curmodule);
        gamma = (uu___255_18332.gamma);
        gamma_sig = (uu___255_18332.gamma_sig);
        gamma_cache = (uu___255_18332.gamma_cache);
        modules = (uu___255_18332.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___255_18332.sigtab);
        attrtab = (uu___255_18332.attrtab);
        is_pattern = (uu___255_18332.is_pattern);
        instantiate_imp = (uu___255_18332.instantiate_imp);
        effects = (uu___255_18332.effects);
        generalize = (uu___255_18332.generalize);
        letrecs = (uu___255_18332.letrecs);
        top_level = (uu___255_18332.top_level);
        check_uvars = (uu___255_18332.check_uvars);
        use_eq = false;
        is_iface = (uu___255_18332.is_iface);
        admit = (uu___255_18332.admit);
        lax = (uu___255_18332.lax);
        lax_universes = (uu___255_18332.lax_universes);
        phase1 = (uu___255_18332.phase1);
        failhard = (uu___255_18332.failhard);
        nosynth = (uu___255_18332.nosynth);
        uvar_subtyping = (uu___255_18332.uvar_subtyping);
        tc_term = (uu___255_18332.tc_term);
        type_of = (uu___255_18332.type_of);
        universe_of = (uu___255_18332.universe_of);
        check_type_of = (uu___255_18332.check_type_of);
        use_bv_sorts = (uu___255_18332.use_bv_sorts);
        qtbl_name_and_index = (uu___255_18332.qtbl_name_and_index);
        normalized_eff_names = (uu___255_18332.normalized_eff_names);
        proof_ns = (uu___255_18332.proof_ns);
        synth_hook = (uu___255_18332.synth_hook);
        splice = (uu___255_18332.splice);
        is_native_tactic = (uu___255_18332.is_native_tactic);
        identifier_info = (uu___255_18332.identifier_info);
        tc_hooks = (uu___255_18332.tc_hooks);
        dsenv = (uu___255_18332.dsenv);
        dep_graph = (uu___255_18332.dep_graph)
      }), uu____18326)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____18342 =
      let uu____18345 = FStar_Ident.id_of_text ""  in [uu____18345]  in
    FStar_Ident.lid_of_ids uu____18342  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____18351 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____18351
        then
          let uu____18354 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____18354 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___256_18381 = env  in
       {
         solver = (uu___256_18381.solver);
         range = (uu___256_18381.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___256_18381.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___256_18381.expected_typ);
         sigtab = (uu___256_18381.sigtab);
         attrtab = (uu___256_18381.attrtab);
         is_pattern = (uu___256_18381.is_pattern);
         instantiate_imp = (uu___256_18381.instantiate_imp);
         effects = (uu___256_18381.effects);
         generalize = (uu___256_18381.generalize);
         letrecs = (uu___256_18381.letrecs);
         top_level = (uu___256_18381.top_level);
         check_uvars = (uu___256_18381.check_uvars);
         use_eq = (uu___256_18381.use_eq);
         is_iface = (uu___256_18381.is_iface);
         admit = (uu___256_18381.admit);
         lax = (uu___256_18381.lax);
         lax_universes = (uu___256_18381.lax_universes);
         phase1 = (uu___256_18381.phase1);
         failhard = (uu___256_18381.failhard);
         nosynth = (uu___256_18381.nosynth);
         uvar_subtyping = (uu___256_18381.uvar_subtyping);
         tc_term = (uu___256_18381.tc_term);
         type_of = (uu___256_18381.type_of);
         universe_of = (uu___256_18381.universe_of);
         check_type_of = (uu___256_18381.check_type_of);
         use_bv_sorts = (uu___256_18381.use_bv_sorts);
         qtbl_name_and_index = (uu___256_18381.qtbl_name_and_index);
         normalized_eff_names = (uu___256_18381.normalized_eff_names);
         proof_ns = (uu___256_18381.proof_ns);
         synth_hook = (uu___256_18381.synth_hook);
         splice = (uu___256_18381.splice);
         is_native_tactic = (uu___256_18381.is_native_tactic);
         identifier_info = (uu___256_18381.identifier_info);
         tc_hooks = (uu___256_18381.tc_hooks);
         dsenv = (uu___256_18381.dsenv);
         dep_graph = (uu___256_18381.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18432)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18436,(uu____18437,t)))::tl1
          ->
          let uu____18458 =
            let uu____18461 = FStar_Syntax_Free.uvars t  in
            ext out uu____18461  in
          aux uu____18458 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18464;
            FStar_Syntax_Syntax.index = uu____18465;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18472 =
            let uu____18475 = FStar_Syntax_Free.uvars t  in
            ext out uu____18475  in
          aux uu____18472 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18532)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18536,(uu____18537,t)))::tl1
          ->
          let uu____18558 =
            let uu____18561 = FStar_Syntax_Free.univs t  in
            ext out uu____18561  in
          aux uu____18558 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18564;
            FStar_Syntax_Syntax.index = uu____18565;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18572 =
            let uu____18575 = FStar_Syntax_Free.univs t  in
            ext out uu____18575  in
          aux uu____18572 tl1
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
          let uu____18636 = FStar_Util.set_add uname out  in
          aux uu____18636 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18639,(uu____18640,t)))::tl1
          ->
          let uu____18661 =
            let uu____18664 = FStar_Syntax_Free.univnames t  in
            ext out uu____18664  in
          aux uu____18661 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18667;
            FStar_Syntax_Syntax.index = uu____18668;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18675 =
            let uu____18678 = FStar_Syntax_Free.univnames t  in
            ext out uu____18678  in
          aux uu____18675 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___230_18698  ->
            match uu___230_18698 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18702 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____18715 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____18725 =
      let uu____18732 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____18732
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____18725 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____18770 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___231_18780  ->
              match uu___231_18780 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____18782 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____18782
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____18785) ->
                  let uu____18802 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____18802))
       in
    FStar_All.pipe_right uu____18770 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___232_18809  ->
    match uu___232_18809 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____18811 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____18811
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18831  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18873) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18892,uu____18893) -> false  in
      let uu____18902 =
        FStar_List.tryFind
          (fun uu____18920  ->
             match uu____18920 with | (p,uu____18928) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18902 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18939,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18961 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18961
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___257_18979 = e  in
        {
          solver = (uu___257_18979.solver);
          range = (uu___257_18979.range);
          curmodule = (uu___257_18979.curmodule);
          gamma = (uu___257_18979.gamma);
          gamma_sig = (uu___257_18979.gamma_sig);
          gamma_cache = (uu___257_18979.gamma_cache);
          modules = (uu___257_18979.modules);
          expected_typ = (uu___257_18979.expected_typ);
          sigtab = (uu___257_18979.sigtab);
          attrtab = (uu___257_18979.attrtab);
          is_pattern = (uu___257_18979.is_pattern);
          instantiate_imp = (uu___257_18979.instantiate_imp);
          effects = (uu___257_18979.effects);
          generalize = (uu___257_18979.generalize);
          letrecs = (uu___257_18979.letrecs);
          top_level = (uu___257_18979.top_level);
          check_uvars = (uu___257_18979.check_uvars);
          use_eq = (uu___257_18979.use_eq);
          is_iface = (uu___257_18979.is_iface);
          admit = (uu___257_18979.admit);
          lax = (uu___257_18979.lax);
          lax_universes = (uu___257_18979.lax_universes);
          phase1 = (uu___257_18979.phase1);
          failhard = (uu___257_18979.failhard);
          nosynth = (uu___257_18979.nosynth);
          uvar_subtyping = (uu___257_18979.uvar_subtyping);
          tc_term = (uu___257_18979.tc_term);
          type_of = (uu___257_18979.type_of);
          universe_of = (uu___257_18979.universe_of);
          check_type_of = (uu___257_18979.check_type_of);
          use_bv_sorts = (uu___257_18979.use_bv_sorts);
          qtbl_name_and_index = (uu___257_18979.qtbl_name_and_index);
          normalized_eff_names = (uu___257_18979.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___257_18979.synth_hook);
          splice = (uu___257_18979.splice);
          is_native_tactic = (uu___257_18979.is_native_tactic);
          identifier_info = (uu___257_18979.identifier_info);
          tc_hooks = (uu___257_18979.tc_hooks);
          dsenv = (uu___257_18979.dsenv);
          dep_graph = (uu___257_18979.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___258_19019 = e  in
      {
        solver = (uu___258_19019.solver);
        range = (uu___258_19019.range);
        curmodule = (uu___258_19019.curmodule);
        gamma = (uu___258_19019.gamma);
        gamma_sig = (uu___258_19019.gamma_sig);
        gamma_cache = (uu___258_19019.gamma_cache);
        modules = (uu___258_19019.modules);
        expected_typ = (uu___258_19019.expected_typ);
        sigtab = (uu___258_19019.sigtab);
        attrtab = (uu___258_19019.attrtab);
        is_pattern = (uu___258_19019.is_pattern);
        instantiate_imp = (uu___258_19019.instantiate_imp);
        effects = (uu___258_19019.effects);
        generalize = (uu___258_19019.generalize);
        letrecs = (uu___258_19019.letrecs);
        top_level = (uu___258_19019.top_level);
        check_uvars = (uu___258_19019.check_uvars);
        use_eq = (uu___258_19019.use_eq);
        is_iface = (uu___258_19019.is_iface);
        admit = (uu___258_19019.admit);
        lax = (uu___258_19019.lax);
        lax_universes = (uu___258_19019.lax_universes);
        phase1 = (uu___258_19019.phase1);
        failhard = (uu___258_19019.failhard);
        nosynth = (uu___258_19019.nosynth);
        uvar_subtyping = (uu___258_19019.uvar_subtyping);
        tc_term = (uu___258_19019.tc_term);
        type_of = (uu___258_19019.type_of);
        universe_of = (uu___258_19019.universe_of);
        check_type_of = (uu___258_19019.check_type_of);
        use_bv_sorts = (uu___258_19019.use_bv_sorts);
        qtbl_name_and_index = (uu___258_19019.qtbl_name_and_index);
        normalized_eff_names = (uu___258_19019.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___258_19019.synth_hook);
        splice = (uu___258_19019.splice);
        is_native_tactic = (uu___258_19019.is_native_tactic);
        identifier_info = (uu___258_19019.identifier_info);
        tc_hooks = (uu___258_19019.tc_hooks);
        dsenv = (uu___258_19019.dsenv);
        dep_graph = (uu___258_19019.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____19034 = FStar_Syntax_Free.names t  in
      let uu____19037 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____19034 uu____19037
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____19058 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____19058
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____19066 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____19066
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____19083 =
      match uu____19083 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____19093 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____19093)
       in
    let uu____19095 =
      let uu____19098 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____19098 FStar_List.rev  in
    FStar_All.pipe_right uu____19095 (FStar_String.concat " ")
  
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
             (fun imp  ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____19151 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____19151 with
                   | FStar_Pervasives_Native.Some uu____19154 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____19155 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____19161;
        univ_ineqs = uu____19162; implicits = uu____19163;_} -> true
    | uu____19174 -> false
  
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
          let uu___259_19201 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___259_19201.deferred);
            univ_ineqs = (uu___259_19201.univ_ineqs);
            implicits = (uu___259_19201.implicits)
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
          let uu____19236 = FStar_Options.defensive ()  in
          if uu____19236
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____19240 =
              let uu____19241 =
                let uu____19242 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____19242  in
              Prims.op_Negation uu____19241  in
            (if uu____19240
             then
               let uu____19247 =
                 let uu____19252 =
                   let uu____19253 = FStar_Syntax_Print.term_to_string t  in
                   let uu____19254 =
                     let uu____19255 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____19255
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____19253 uu____19254
                    in
                 (FStar_Errors.Warning_Defensive, uu____19252)  in
               FStar_Errors.log_issue rng uu____19247
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
          let uu____19286 =
            let uu____19287 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19287  in
          if uu____19286
          then ()
          else
            (let uu____19289 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____19289 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____19312 =
            let uu____19313 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19313  in
          if uu____19312
          then ()
          else
            (let uu____19315 = bound_vars e  in
             def_check_closed_in rng msg uu____19315 t)
  
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
          let uu___260_19350 = g  in
          let uu____19351 =
            let uu____19352 =
              let uu____19353 =
                let uu____19360 =
                  let uu____19361 =
                    let uu____19376 =
                      let uu____19385 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____19385]  in
                    (f, uu____19376)  in
                  FStar_Syntax_Syntax.Tm_app uu____19361  in
                FStar_Syntax_Syntax.mk uu____19360  in
              uu____19353 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____19352
             in
          {
            guard_f = uu____19351;
            deferred = (uu___260_19350.deferred);
            univ_ineqs = (uu___260_19350.univ_ineqs);
            implicits = (uu___260_19350.implicits)
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
          let uu___261_19433 = g  in
          let uu____19434 =
            let uu____19435 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19435  in
          {
            guard_f = uu____19434;
            deferred = (uu___261_19433.deferred);
            univ_ineqs = (uu___261_19433.univ_ineqs);
            implicits = (uu___261_19433.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19441 ->
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
          let uu____19456 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19456
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19462 =
      let uu____19463 = FStar_Syntax_Util.unmeta t  in
      uu____19463.FStar_Syntax_Syntax.n  in
    match uu____19462 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19467 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____19508 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19508;
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
                       let uu____19585 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____19585
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___262_19587 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___262_19587.deferred);
              univ_ineqs = (uu___262_19587.univ_ineqs);
              implicits = (uu___262_19587.implicits)
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
               let uu____19616 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____19616
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
            let uu___263_19635 = g  in
            let uu____19636 =
              let uu____19637 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____19637  in
            {
              guard_f = uu____19636;
              deferred = (uu___263_19635.deferred);
              univ_ineqs = (uu___263_19635.univ_ineqs);
              implicits = (uu___263_19635.implicits)
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
            let uu____19675 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____19675 with
            | FStar_Pervasives_Native.Some
                (uu____19698::(tm,uu____19700)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____19750 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____19766 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____19766;
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
                  let imp =
                    {
                      imp_reason = reason;
                      imp_uvar = ctx_uvar;
                      imp_tm = t;
                      imp_range = r
                    }  in
                  let g =
                    let uu___264_19797 = trivial_guard  in
                    {
                      guard_f = (uu___264_19797.guard_f);
                      deferred = (uu___264_19797.deferred);
                      univ_ineqs = (uu___264_19797.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____19814  -> ());
    push = (fun uu____19816  -> ());
    pop = (fun uu____19818  -> ());
    snapshot =
      (fun uu____19820  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____19829  -> fun uu____19830  -> ());
    encode_modul = (fun uu____19841  -> fun uu____19842  -> ());
    encode_sig = (fun uu____19845  -> fun uu____19846  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____19852 =
             let uu____19859 = FStar_Options.peek ()  in (e, g, uu____19859)
              in
           [uu____19852]);
    solve = (fun uu____19875  -> fun uu____19876  -> fun uu____19877  -> ());
    finish = (fun uu____19883  -> ());
    refresh = (fun uu____19885  -> ())
  } 