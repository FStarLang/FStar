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
  imp_range: FStar_Range.range ;
  imp_meta:
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
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
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_range
  
let (__proj__Mkimplicit__item__imp_meta :
  implicit ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_meta
  
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
           (fun uu___219_8876  ->
              match uu___219_8876 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8879 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8879  in
                  let uu____8880 =
                    let uu____8881 = FStar_Syntax_Subst.compress y  in
                    uu____8881.FStar_Syntax_Syntax.n  in
                  (match uu____8880 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8885 =
                         let uu___233_8886 = y1  in
                         let uu____8887 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___233_8886.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___233_8886.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8887
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8885
                   | uu____8890 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___234_8902 = env  in
      let uu____8903 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___234_8902.solver);
        range = (uu___234_8902.range);
        curmodule = (uu___234_8902.curmodule);
        gamma = uu____8903;
        gamma_sig = (uu___234_8902.gamma_sig);
        gamma_cache = (uu___234_8902.gamma_cache);
        modules = (uu___234_8902.modules);
        expected_typ = (uu___234_8902.expected_typ);
        sigtab = (uu___234_8902.sigtab);
        attrtab = (uu___234_8902.attrtab);
        is_pattern = (uu___234_8902.is_pattern);
        instantiate_imp = (uu___234_8902.instantiate_imp);
        effects = (uu___234_8902.effects);
        generalize = (uu___234_8902.generalize);
        letrecs = (uu___234_8902.letrecs);
        top_level = (uu___234_8902.top_level);
        check_uvars = (uu___234_8902.check_uvars);
        use_eq = (uu___234_8902.use_eq);
        is_iface = (uu___234_8902.is_iface);
        admit = (uu___234_8902.admit);
        lax = (uu___234_8902.lax);
        lax_universes = (uu___234_8902.lax_universes);
        phase1 = (uu___234_8902.phase1);
        failhard = (uu___234_8902.failhard);
        nosynth = (uu___234_8902.nosynth);
        uvar_subtyping = (uu___234_8902.uvar_subtyping);
        tc_term = (uu___234_8902.tc_term);
        type_of = (uu___234_8902.type_of);
        universe_of = (uu___234_8902.universe_of);
        check_type_of = (uu___234_8902.check_type_of);
        use_bv_sorts = (uu___234_8902.use_bv_sorts);
        qtbl_name_and_index = (uu___234_8902.qtbl_name_and_index);
        normalized_eff_names = (uu___234_8902.normalized_eff_names);
        proof_ns = (uu___234_8902.proof_ns);
        synth_hook = (uu___234_8902.synth_hook);
        splice = (uu___234_8902.splice);
        is_native_tactic = (uu___234_8902.is_native_tactic);
        identifier_info = (uu___234_8902.identifier_info);
        tc_hooks = (uu___234_8902.tc_hooks);
        dsenv = (uu___234_8902.dsenv);
        dep_graph = (uu___234_8902.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8910  -> fun uu____8911  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___235_8931 = env  in
      {
        solver = (uu___235_8931.solver);
        range = (uu___235_8931.range);
        curmodule = (uu___235_8931.curmodule);
        gamma = (uu___235_8931.gamma);
        gamma_sig = (uu___235_8931.gamma_sig);
        gamma_cache = (uu___235_8931.gamma_cache);
        modules = (uu___235_8931.modules);
        expected_typ = (uu___235_8931.expected_typ);
        sigtab = (uu___235_8931.sigtab);
        attrtab = (uu___235_8931.attrtab);
        is_pattern = (uu___235_8931.is_pattern);
        instantiate_imp = (uu___235_8931.instantiate_imp);
        effects = (uu___235_8931.effects);
        generalize = (uu___235_8931.generalize);
        letrecs = (uu___235_8931.letrecs);
        top_level = (uu___235_8931.top_level);
        check_uvars = (uu___235_8931.check_uvars);
        use_eq = (uu___235_8931.use_eq);
        is_iface = (uu___235_8931.is_iface);
        admit = (uu___235_8931.admit);
        lax = (uu___235_8931.lax);
        lax_universes = (uu___235_8931.lax_universes);
        phase1 = (uu___235_8931.phase1);
        failhard = (uu___235_8931.failhard);
        nosynth = (uu___235_8931.nosynth);
        uvar_subtyping = (uu___235_8931.uvar_subtyping);
        tc_term = (uu___235_8931.tc_term);
        type_of = (uu___235_8931.type_of);
        universe_of = (uu___235_8931.universe_of);
        check_type_of = (uu___235_8931.check_type_of);
        use_bv_sorts = (uu___235_8931.use_bv_sorts);
        qtbl_name_and_index = (uu___235_8931.qtbl_name_and_index);
        normalized_eff_names = (uu___235_8931.normalized_eff_names);
        proof_ns = (uu___235_8931.proof_ns);
        synth_hook = (uu___235_8931.synth_hook);
        splice = (uu___235_8931.splice);
        is_native_tactic = (uu___235_8931.is_native_tactic);
        identifier_info = (uu___235_8931.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___235_8931.dsenv);
        dep_graph = (uu___235_8931.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___236_8942 = e  in
      {
        solver = (uu___236_8942.solver);
        range = (uu___236_8942.range);
        curmodule = (uu___236_8942.curmodule);
        gamma = (uu___236_8942.gamma);
        gamma_sig = (uu___236_8942.gamma_sig);
        gamma_cache = (uu___236_8942.gamma_cache);
        modules = (uu___236_8942.modules);
        expected_typ = (uu___236_8942.expected_typ);
        sigtab = (uu___236_8942.sigtab);
        attrtab = (uu___236_8942.attrtab);
        is_pattern = (uu___236_8942.is_pattern);
        instantiate_imp = (uu___236_8942.instantiate_imp);
        effects = (uu___236_8942.effects);
        generalize = (uu___236_8942.generalize);
        letrecs = (uu___236_8942.letrecs);
        top_level = (uu___236_8942.top_level);
        check_uvars = (uu___236_8942.check_uvars);
        use_eq = (uu___236_8942.use_eq);
        is_iface = (uu___236_8942.is_iface);
        admit = (uu___236_8942.admit);
        lax = (uu___236_8942.lax);
        lax_universes = (uu___236_8942.lax_universes);
        phase1 = (uu___236_8942.phase1);
        failhard = (uu___236_8942.failhard);
        nosynth = (uu___236_8942.nosynth);
        uvar_subtyping = (uu___236_8942.uvar_subtyping);
        tc_term = (uu___236_8942.tc_term);
        type_of = (uu___236_8942.type_of);
        universe_of = (uu___236_8942.universe_of);
        check_type_of = (uu___236_8942.check_type_of);
        use_bv_sorts = (uu___236_8942.use_bv_sorts);
        qtbl_name_and_index = (uu___236_8942.qtbl_name_and_index);
        normalized_eff_names = (uu___236_8942.normalized_eff_names);
        proof_ns = (uu___236_8942.proof_ns);
        synth_hook = (uu___236_8942.synth_hook);
        splice = (uu___236_8942.splice);
        is_native_tactic = (uu___236_8942.is_native_tactic);
        identifier_info = (uu___236_8942.identifier_info);
        tc_hooks = (uu___236_8942.tc_hooks);
        dsenv = (uu___236_8942.dsenv);
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
      | (NoDelta ,uu____8965) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8966,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8967,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8968 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8977 . unit -> 'Auu____8977 FStar_Util.smap =
  fun uu____8984  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8989 . unit -> 'Auu____8989 FStar_Util.smap =
  fun uu____8996  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____9106 = new_gamma_cache ()  in
                let uu____9109 = new_sigtab ()  in
                let uu____9112 = new_sigtab ()  in
                let uu____9119 =
                  let uu____9132 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____9132, FStar_Pervasives_Native.None)  in
                let uu____9147 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____9150 = FStar_Options.using_facts_from ()  in
                let uu____9151 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____9154 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____9106;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____9109;
                  attrtab = uu____9112;
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
                  qtbl_name_and_index = uu____9119;
                  normalized_eff_names = uu____9147;
                  proof_ns = uu____9150;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____9190  -> false);
                  identifier_info = uu____9151;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____9154;
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
  fun uu____9290  ->
    let uu____9291 = FStar_ST.op_Bang query_indices  in
    match uu____9291 with
    | [] -> failwith "Empty query indices!"
    | uu____9345 ->
        let uu____9354 =
          let uu____9363 =
            let uu____9370 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____9370  in
          let uu____9424 = FStar_ST.op_Bang query_indices  in uu____9363 ::
            uu____9424
           in
        FStar_ST.op_Colon_Equals query_indices uu____9354
  
let (pop_query_indices : unit -> unit) =
  fun uu____9521  ->
    let uu____9522 = FStar_ST.op_Bang query_indices  in
    match uu____9522 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9645  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9675  ->
    match uu____9675 with
    | (l,n1) ->
        let uu____9682 = FStar_ST.op_Bang query_indices  in
        (match uu____9682 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9801 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9820  ->
    let uu____9821 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9821
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9898 =
       let uu____9901 = FStar_ST.op_Bang stack  in env :: uu____9901  in
     FStar_ST.op_Colon_Equals stack uu____9898);
    (let uu___237_9958 = env  in
     let uu____9959 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9962 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9965 = FStar_Util.smap_copy (attrtab env)  in
     let uu____9972 =
       let uu____9985 =
         let uu____9988 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9988  in
       let uu____10013 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9985, uu____10013)  in
     let uu____10054 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____10057 =
       let uu____10060 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____10060  in
     {
       solver = (uu___237_9958.solver);
       range = (uu___237_9958.range);
       curmodule = (uu___237_9958.curmodule);
       gamma = (uu___237_9958.gamma);
       gamma_sig = (uu___237_9958.gamma_sig);
       gamma_cache = uu____9959;
       modules = (uu___237_9958.modules);
       expected_typ = (uu___237_9958.expected_typ);
       sigtab = uu____9962;
       attrtab = uu____9965;
       is_pattern = (uu___237_9958.is_pattern);
       instantiate_imp = (uu___237_9958.instantiate_imp);
       effects = (uu___237_9958.effects);
       generalize = (uu___237_9958.generalize);
       letrecs = (uu___237_9958.letrecs);
       top_level = (uu___237_9958.top_level);
       check_uvars = (uu___237_9958.check_uvars);
       use_eq = (uu___237_9958.use_eq);
       is_iface = (uu___237_9958.is_iface);
       admit = (uu___237_9958.admit);
       lax = (uu___237_9958.lax);
       lax_universes = (uu___237_9958.lax_universes);
       phase1 = (uu___237_9958.phase1);
       failhard = (uu___237_9958.failhard);
       nosynth = (uu___237_9958.nosynth);
       uvar_subtyping = (uu___237_9958.uvar_subtyping);
       tc_term = (uu___237_9958.tc_term);
       type_of = (uu___237_9958.type_of);
       universe_of = (uu___237_9958.universe_of);
       check_type_of = (uu___237_9958.check_type_of);
       use_bv_sorts = (uu___237_9958.use_bv_sorts);
       qtbl_name_and_index = uu____9972;
       normalized_eff_names = uu____10054;
       proof_ns = (uu___237_9958.proof_ns);
       synth_hook = (uu___237_9958.synth_hook);
       splice = (uu___237_9958.splice);
       is_native_tactic = (uu___237_9958.is_native_tactic);
       identifier_info = uu____10057;
       tc_hooks = (uu___237_9958.tc_hooks);
       dsenv = (uu___237_9958.dsenv);
       dep_graph = (uu___237_9958.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____10110  ->
    let uu____10111 = FStar_ST.op_Bang stack  in
    match uu____10111 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10173 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____10245  ->
           let uu____10246 = snapshot_stack env  in
           match uu____10246 with
           | (stack_depth,env1) ->
               let uu____10271 = snapshot_query_indices ()  in
               (match uu____10271 with
                | (query_indices_depth,()) ->
                    let uu____10295 = (env1.solver).snapshot msg  in
                    (match uu____10295 with
                     | (solver_depth,()) ->
                         let uu____10337 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____10337 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___238_10383 = env1  in
                                 {
                                   solver = (uu___238_10383.solver);
                                   range = (uu___238_10383.range);
                                   curmodule = (uu___238_10383.curmodule);
                                   gamma = (uu___238_10383.gamma);
                                   gamma_sig = (uu___238_10383.gamma_sig);
                                   gamma_cache = (uu___238_10383.gamma_cache);
                                   modules = (uu___238_10383.modules);
                                   expected_typ =
                                     (uu___238_10383.expected_typ);
                                   sigtab = (uu___238_10383.sigtab);
                                   attrtab = (uu___238_10383.attrtab);
                                   is_pattern = (uu___238_10383.is_pattern);
                                   instantiate_imp =
                                     (uu___238_10383.instantiate_imp);
                                   effects = (uu___238_10383.effects);
                                   generalize = (uu___238_10383.generalize);
                                   letrecs = (uu___238_10383.letrecs);
                                   top_level = (uu___238_10383.top_level);
                                   check_uvars = (uu___238_10383.check_uvars);
                                   use_eq = (uu___238_10383.use_eq);
                                   is_iface = (uu___238_10383.is_iface);
                                   admit = (uu___238_10383.admit);
                                   lax = (uu___238_10383.lax);
                                   lax_universes =
                                     (uu___238_10383.lax_universes);
                                   phase1 = (uu___238_10383.phase1);
                                   failhard = (uu___238_10383.failhard);
                                   nosynth = (uu___238_10383.nosynth);
                                   uvar_subtyping =
                                     (uu___238_10383.uvar_subtyping);
                                   tc_term = (uu___238_10383.tc_term);
                                   type_of = (uu___238_10383.type_of);
                                   universe_of = (uu___238_10383.universe_of);
                                   check_type_of =
                                     (uu___238_10383.check_type_of);
                                   use_bv_sorts =
                                     (uu___238_10383.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___238_10383.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___238_10383.normalized_eff_names);
                                   proof_ns = (uu___238_10383.proof_ns);
                                   synth_hook = (uu___238_10383.synth_hook);
                                   splice = (uu___238_10383.splice);
                                   is_native_tactic =
                                     (uu___238_10383.is_native_tactic);
                                   identifier_info =
                                     (uu___238_10383.identifier_info);
                                   tc_hooks = (uu___238_10383.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___238_10383.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____10414  ->
             let uu____10415 =
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
             match uu____10415 with
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
                             ((let uu____10541 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____10541
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____10552 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____10552
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____10579,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____10611 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10637  ->
                  match uu____10637 with
                  | (m,uu____10643) -> FStar_Ident.lid_equals l m))
           in
        (match uu____10611 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___239_10651 = env  in
               {
                 solver = (uu___239_10651.solver);
                 range = (uu___239_10651.range);
                 curmodule = (uu___239_10651.curmodule);
                 gamma = (uu___239_10651.gamma);
                 gamma_sig = (uu___239_10651.gamma_sig);
                 gamma_cache = (uu___239_10651.gamma_cache);
                 modules = (uu___239_10651.modules);
                 expected_typ = (uu___239_10651.expected_typ);
                 sigtab = (uu___239_10651.sigtab);
                 attrtab = (uu___239_10651.attrtab);
                 is_pattern = (uu___239_10651.is_pattern);
                 instantiate_imp = (uu___239_10651.instantiate_imp);
                 effects = (uu___239_10651.effects);
                 generalize = (uu___239_10651.generalize);
                 letrecs = (uu___239_10651.letrecs);
                 top_level = (uu___239_10651.top_level);
                 check_uvars = (uu___239_10651.check_uvars);
                 use_eq = (uu___239_10651.use_eq);
                 is_iface = (uu___239_10651.is_iface);
                 admit = (uu___239_10651.admit);
                 lax = (uu___239_10651.lax);
                 lax_universes = (uu___239_10651.lax_universes);
                 phase1 = (uu___239_10651.phase1);
                 failhard = (uu___239_10651.failhard);
                 nosynth = (uu___239_10651.nosynth);
                 uvar_subtyping = (uu___239_10651.uvar_subtyping);
                 tc_term = (uu___239_10651.tc_term);
                 type_of = (uu___239_10651.type_of);
                 universe_of = (uu___239_10651.universe_of);
                 check_type_of = (uu___239_10651.check_type_of);
                 use_bv_sorts = (uu___239_10651.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___239_10651.normalized_eff_names);
                 proof_ns = (uu___239_10651.proof_ns);
                 synth_hook = (uu___239_10651.synth_hook);
                 splice = (uu___239_10651.splice);
                 is_native_tactic = (uu___239_10651.is_native_tactic);
                 identifier_info = (uu___239_10651.identifier_info);
                 tc_hooks = (uu___239_10651.tc_hooks);
                 dsenv = (uu___239_10651.dsenv);
                 dep_graph = (uu___239_10651.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____10664,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_10673 = env  in
               {
                 solver = (uu___240_10673.solver);
                 range = (uu___240_10673.range);
                 curmodule = (uu___240_10673.curmodule);
                 gamma = (uu___240_10673.gamma);
                 gamma_sig = (uu___240_10673.gamma_sig);
                 gamma_cache = (uu___240_10673.gamma_cache);
                 modules = (uu___240_10673.modules);
                 expected_typ = (uu___240_10673.expected_typ);
                 sigtab = (uu___240_10673.sigtab);
                 attrtab = (uu___240_10673.attrtab);
                 is_pattern = (uu___240_10673.is_pattern);
                 instantiate_imp = (uu___240_10673.instantiate_imp);
                 effects = (uu___240_10673.effects);
                 generalize = (uu___240_10673.generalize);
                 letrecs = (uu___240_10673.letrecs);
                 top_level = (uu___240_10673.top_level);
                 check_uvars = (uu___240_10673.check_uvars);
                 use_eq = (uu___240_10673.use_eq);
                 is_iface = (uu___240_10673.is_iface);
                 admit = (uu___240_10673.admit);
                 lax = (uu___240_10673.lax);
                 lax_universes = (uu___240_10673.lax_universes);
                 phase1 = (uu___240_10673.phase1);
                 failhard = (uu___240_10673.failhard);
                 nosynth = (uu___240_10673.nosynth);
                 uvar_subtyping = (uu___240_10673.uvar_subtyping);
                 tc_term = (uu___240_10673.tc_term);
                 type_of = (uu___240_10673.type_of);
                 universe_of = (uu___240_10673.universe_of);
                 check_type_of = (uu___240_10673.check_type_of);
                 use_bv_sorts = (uu___240_10673.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_10673.normalized_eff_names);
                 proof_ns = (uu___240_10673.proof_ns);
                 synth_hook = (uu___240_10673.synth_hook);
                 splice = (uu___240_10673.splice);
                 is_native_tactic = (uu___240_10673.is_native_tactic);
                 identifier_info = (uu___240_10673.identifier_info);
                 tc_hooks = (uu___240_10673.tc_hooks);
                 dsenv = (uu___240_10673.dsenv);
                 dep_graph = (uu___240_10673.dep_graph)
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
        (let uu___241_10707 = e  in
         {
           solver = (uu___241_10707.solver);
           range = r;
           curmodule = (uu___241_10707.curmodule);
           gamma = (uu___241_10707.gamma);
           gamma_sig = (uu___241_10707.gamma_sig);
           gamma_cache = (uu___241_10707.gamma_cache);
           modules = (uu___241_10707.modules);
           expected_typ = (uu___241_10707.expected_typ);
           sigtab = (uu___241_10707.sigtab);
           attrtab = (uu___241_10707.attrtab);
           is_pattern = (uu___241_10707.is_pattern);
           instantiate_imp = (uu___241_10707.instantiate_imp);
           effects = (uu___241_10707.effects);
           generalize = (uu___241_10707.generalize);
           letrecs = (uu___241_10707.letrecs);
           top_level = (uu___241_10707.top_level);
           check_uvars = (uu___241_10707.check_uvars);
           use_eq = (uu___241_10707.use_eq);
           is_iface = (uu___241_10707.is_iface);
           admit = (uu___241_10707.admit);
           lax = (uu___241_10707.lax);
           lax_universes = (uu___241_10707.lax_universes);
           phase1 = (uu___241_10707.phase1);
           failhard = (uu___241_10707.failhard);
           nosynth = (uu___241_10707.nosynth);
           uvar_subtyping = (uu___241_10707.uvar_subtyping);
           tc_term = (uu___241_10707.tc_term);
           type_of = (uu___241_10707.type_of);
           universe_of = (uu___241_10707.universe_of);
           check_type_of = (uu___241_10707.check_type_of);
           use_bv_sorts = (uu___241_10707.use_bv_sorts);
           qtbl_name_and_index = (uu___241_10707.qtbl_name_and_index);
           normalized_eff_names = (uu___241_10707.normalized_eff_names);
           proof_ns = (uu___241_10707.proof_ns);
           synth_hook = (uu___241_10707.synth_hook);
           splice = (uu___241_10707.splice);
           is_native_tactic = (uu___241_10707.is_native_tactic);
           identifier_info = (uu___241_10707.identifier_info);
           tc_hooks = (uu___241_10707.tc_hooks);
           dsenv = (uu___241_10707.dsenv);
           dep_graph = (uu___241_10707.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10723 =
        let uu____10724 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10724 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10723
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10786 =
          let uu____10787 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10787 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10786
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10849 =
          let uu____10850 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10850 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10849
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10912 =
        let uu____10913 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10913 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10912
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___242_10982 = env  in
      {
        solver = (uu___242_10982.solver);
        range = (uu___242_10982.range);
        curmodule = lid;
        gamma = (uu___242_10982.gamma);
        gamma_sig = (uu___242_10982.gamma_sig);
        gamma_cache = (uu___242_10982.gamma_cache);
        modules = (uu___242_10982.modules);
        expected_typ = (uu___242_10982.expected_typ);
        sigtab = (uu___242_10982.sigtab);
        attrtab = (uu___242_10982.attrtab);
        is_pattern = (uu___242_10982.is_pattern);
        instantiate_imp = (uu___242_10982.instantiate_imp);
        effects = (uu___242_10982.effects);
        generalize = (uu___242_10982.generalize);
        letrecs = (uu___242_10982.letrecs);
        top_level = (uu___242_10982.top_level);
        check_uvars = (uu___242_10982.check_uvars);
        use_eq = (uu___242_10982.use_eq);
        is_iface = (uu___242_10982.is_iface);
        admit = (uu___242_10982.admit);
        lax = (uu___242_10982.lax);
        lax_universes = (uu___242_10982.lax_universes);
        phase1 = (uu___242_10982.phase1);
        failhard = (uu___242_10982.failhard);
        nosynth = (uu___242_10982.nosynth);
        uvar_subtyping = (uu___242_10982.uvar_subtyping);
        tc_term = (uu___242_10982.tc_term);
        type_of = (uu___242_10982.type_of);
        universe_of = (uu___242_10982.universe_of);
        check_type_of = (uu___242_10982.check_type_of);
        use_bv_sorts = (uu___242_10982.use_bv_sorts);
        qtbl_name_and_index = (uu___242_10982.qtbl_name_and_index);
        normalized_eff_names = (uu___242_10982.normalized_eff_names);
        proof_ns = (uu___242_10982.proof_ns);
        synth_hook = (uu___242_10982.synth_hook);
        splice = (uu___242_10982.splice);
        is_native_tactic = (uu___242_10982.is_native_tactic);
        identifier_info = (uu___242_10982.identifier_info);
        tc_hooks = (uu___242_10982.tc_hooks);
        dsenv = (uu___242_10982.dsenv);
        dep_graph = (uu___242_10982.dep_graph)
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
      let uu____11009 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11009
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11019 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11019)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11029 =
      let uu____11030 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11030  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11029)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11035  ->
    let uu____11036 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11036
  
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
      | ((formals,t),uu____11092) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____11126 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11126)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___220_11142  ->
    match uu___220_11142 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11168  -> new_u_univ ()))
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
      let uu____11187 = inst_tscheme t  in
      match uu____11187 with
      | (us,t1) ->
          let uu____11198 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11198)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11218  ->
          match uu____11218 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11239 =
                         let uu____11240 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____11241 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____11242 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____11243 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11240 uu____11241 uu____11242 uu____11243
                          in
                       failwith uu____11239)
                    else ();
                    (let uu____11245 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____11245))
               | uu____11254 ->
                   let uu____11255 =
                     let uu____11256 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____11256
                      in
                   failwith uu____11255)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____11262 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11268 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11274 -> false
  
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
             | ([],uu____11316) -> Maybe
             | (uu____11323,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____11342 -> No  in
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
          let uu____11433 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____11433 with
          | FStar_Pervasives_Native.None  ->
              let uu____11456 =
                FStar_Util.find_map env.gamma
                  (fun uu___221_11500  ->
                     match uu___221_11500 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11539 = FStar_Ident.lid_equals lid l  in
                         if uu____11539
                         then
                           let uu____11560 =
                             let uu____11579 =
                               let uu____11594 = inst_tscheme t  in
                               FStar_Util.Inl uu____11594  in
                             let uu____11609 = FStar_Ident.range_of_lid l  in
                             (uu____11579, uu____11609)  in
                           FStar_Pervasives_Native.Some uu____11560
                         else FStar_Pervasives_Native.None
                     | uu____11661 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11456
                (fun uu____11699  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___222_11708  ->
                        match uu___222_11708 with
                        | (uu____11711,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11713);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11714;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11715;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11716;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11717;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11737 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11737
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
                                  uu____11785 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11792 -> cache t  in
                            let uu____11793 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11793 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11799 =
                                   let uu____11800 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11800)
                                    in
                                 maybe_cache uu____11799)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11868 = find_in_sigtab env lid  in
         match uu____11868 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____11948 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____11948 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____11990 =
          let uu____11993 = lookup_attr env1 attr  in se1 :: uu____11993  in
        FStar_Util.smap_add (attrtab env1) attr uu____11990  in
      FStar_List.iter
        (fun attr  ->
           let uu____12003 =
             let uu____12004 = FStar_Syntax_Subst.compress attr  in
             uu____12004.FStar_Syntax_Syntax.n  in
           match uu____12003 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____12008 =
                 let uu____12009 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____12009.FStar_Ident.str  in
               add_one1 env se uu____12008
           | uu____12010 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12032) ->
          add_sigelts env ses
      | uu____12041 ->
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
            | uu____12056 -> ()))

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
        (fun uu___223_12087  ->
           match uu___223_12087 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12105 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____12166,lb::[]),uu____12168) ->
            let uu____12175 =
              let uu____12184 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____12193 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____12184, uu____12193)  in
            FStar_Pervasives_Native.Some uu____12175
        | FStar_Syntax_Syntax.Sig_let ((uu____12206,lbs),uu____12208) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____12238 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____12250 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____12250
                     then
                       let uu____12261 =
                         let uu____12270 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____12279 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____12270, uu____12279)  in
                       FStar_Pervasives_Native.Some uu____12261
                     else FStar_Pervasives_Native.None)
        | uu____12301 -> FStar_Pervasives_Native.None
  
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
          let uu____12360 =
            let uu____12369 =
              let uu____12374 =
                let uu____12375 =
                  let uu____12378 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____12378
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____12375)  in
              inst_tscheme1 uu____12374  in
            (uu____12369, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12360
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____12400,uu____12401) ->
          let uu____12406 =
            let uu____12415 =
              let uu____12420 =
                let uu____12421 =
                  let uu____12424 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____12424  in
                (us, uu____12421)  in
              inst_tscheme1 uu____12420  in
            (uu____12415, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12406
      | uu____12443 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12531 =
          match uu____12531 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12627,uvs,t,uu____12630,uu____12631,uu____12632);
                      FStar_Syntax_Syntax.sigrng = uu____12633;
                      FStar_Syntax_Syntax.sigquals = uu____12634;
                      FStar_Syntax_Syntax.sigmeta = uu____12635;
                      FStar_Syntax_Syntax.sigattrs = uu____12636;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12657 =
                     let uu____12666 = inst_tscheme1 (uvs, t)  in
                     (uu____12666, rng)  in
                   FStar_Pervasives_Native.Some uu____12657
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12690;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12692;
                      FStar_Syntax_Syntax.sigattrs = uu____12693;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12710 =
                     let uu____12711 = in_cur_mod env l  in uu____12711 = Yes
                      in
                   if uu____12710
                   then
                     let uu____12722 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12722
                      then
                        let uu____12735 =
                          let uu____12744 = inst_tscheme1 (uvs, t)  in
                          (uu____12744, rng)  in
                        FStar_Pervasives_Native.Some uu____12735
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12775 =
                        let uu____12784 = inst_tscheme1 (uvs, t)  in
                        (uu____12784, rng)  in
                      FStar_Pervasives_Native.Some uu____12775)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12809,uu____12810);
                      FStar_Syntax_Syntax.sigrng = uu____12811;
                      FStar_Syntax_Syntax.sigquals = uu____12812;
                      FStar_Syntax_Syntax.sigmeta = uu____12813;
                      FStar_Syntax_Syntax.sigattrs = uu____12814;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12855 =
                          let uu____12864 = inst_tscheme1 (uvs, k)  in
                          (uu____12864, rng)  in
                        FStar_Pervasives_Native.Some uu____12855
                    | uu____12885 ->
                        let uu____12886 =
                          let uu____12895 =
                            let uu____12900 =
                              let uu____12901 =
                                let uu____12904 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12904
                                 in
                              (uvs, uu____12901)  in
                            inst_tscheme1 uu____12900  in
                          (uu____12895, rng)  in
                        FStar_Pervasives_Native.Some uu____12886)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12927,uu____12928);
                      FStar_Syntax_Syntax.sigrng = uu____12929;
                      FStar_Syntax_Syntax.sigquals = uu____12930;
                      FStar_Syntax_Syntax.sigmeta = uu____12931;
                      FStar_Syntax_Syntax.sigattrs = uu____12932;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12974 =
                          let uu____12983 = inst_tscheme_with (uvs, k) us  in
                          (uu____12983, rng)  in
                        FStar_Pervasives_Native.Some uu____12974
                    | uu____13004 ->
                        let uu____13005 =
                          let uu____13014 =
                            let uu____13019 =
                              let uu____13020 =
                                let uu____13023 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13023
                                 in
                              (uvs, uu____13020)  in
                            inst_tscheme_with uu____13019 us  in
                          (uu____13014, rng)  in
                        FStar_Pervasives_Native.Some uu____13005)
               | FStar_Util.Inr se ->
                   let uu____13059 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13080;
                          FStar_Syntax_Syntax.sigrng = uu____13081;
                          FStar_Syntax_Syntax.sigquals = uu____13082;
                          FStar_Syntax_Syntax.sigmeta = uu____13083;
                          FStar_Syntax_Syntax.sigattrs = uu____13084;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13099 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____13059
                     (FStar_Util.map_option
                        (fun uu____13147  ->
                           match uu____13147 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____13178 =
          let uu____13189 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____13189 mapper  in
        match uu____13178 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____13263 =
              let uu____13274 =
                let uu____13281 =
                  let uu___243_13284 = t  in
                  let uu____13285 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___243_13284.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____13285;
                    FStar_Syntax_Syntax.vars =
                      (uu___243_13284.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____13281)  in
              (uu____13274, r)  in
            FStar_Pervasives_Native.Some uu____13263
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13332 = lookup_qname env l  in
      match uu____13332 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____13351 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____13403 = try_lookup_bv env bv  in
      match uu____13403 with
      | FStar_Pervasives_Native.None  ->
          let uu____13418 = variable_not_found bv  in
          FStar_Errors.raise_error uu____13418 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____13433 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____13434 =
            let uu____13435 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____13435  in
          (uu____13433, uu____13434)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____13456 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____13456 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____13522 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____13522  in
          let uu____13523 =
            let uu____13532 =
              let uu____13537 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13537)  in
            (uu____13532, r1)  in
          FStar_Pervasives_Native.Some uu____13523
  
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
        let uu____13571 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13571 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13604,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13629 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13629  in
            let uu____13630 =
              let uu____13635 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13635, r1)  in
            FStar_Pervasives_Native.Some uu____13630
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13658 = try_lookup_lid env l  in
      match uu____13658 with
      | FStar_Pervasives_Native.None  ->
          let uu____13685 = name_not_found l  in
          let uu____13690 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13685 uu____13690
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___224_13730  ->
              match uu___224_13730 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13732 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13751 = lookup_qname env lid  in
      match uu____13751 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13760,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13763;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13765;
              FStar_Syntax_Syntax.sigattrs = uu____13766;_},FStar_Pervasives_Native.None
            ),uu____13767)
          ->
          let uu____13816 =
            let uu____13823 =
              let uu____13824 =
                let uu____13827 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13827 t  in
              (uvs, uu____13824)  in
            (uu____13823, q)  in
          FStar_Pervasives_Native.Some uu____13816
      | uu____13840 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13861 = lookup_qname env lid  in
      match uu____13861 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13866,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13869;
              FStar_Syntax_Syntax.sigquals = uu____13870;
              FStar_Syntax_Syntax.sigmeta = uu____13871;
              FStar_Syntax_Syntax.sigattrs = uu____13872;_},FStar_Pervasives_Native.None
            ),uu____13873)
          ->
          let uu____13922 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13922 (uvs, t)
      | uu____13927 ->
          let uu____13928 = name_not_found lid  in
          let uu____13933 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13928 uu____13933
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13952 = lookup_qname env lid  in
      match uu____13952 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13957,uvs,t,uu____13960,uu____13961,uu____13962);
              FStar_Syntax_Syntax.sigrng = uu____13963;
              FStar_Syntax_Syntax.sigquals = uu____13964;
              FStar_Syntax_Syntax.sigmeta = uu____13965;
              FStar_Syntax_Syntax.sigattrs = uu____13966;_},FStar_Pervasives_Native.None
            ),uu____13967)
          ->
          let uu____14020 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14020 (uvs, t)
      | uu____14025 ->
          let uu____14026 = name_not_found lid  in
          let uu____14031 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14026 uu____14031
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14052 = lookup_qname env lid  in
      match uu____14052 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14059,uu____14060,uu____14061,uu____14062,uu____14063,dcs);
              FStar_Syntax_Syntax.sigrng = uu____14065;
              FStar_Syntax_Syntax.sigquals = uu____14066;
              FStar_Syntax_Syntax.sigmeta = uu____14067;
              FStar_Syntax_Syntax.sigattrs = uu____14068;_},uu____14069),uu____14070)
          -> (true, dcs)
      | uu____14131 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____14144 = lookup_qname env lid  in
      match uu____14144 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14145,uu____14146,uu____14147,l,uu____14149,uu____14150);
              FStar_Syntax_Syntax.sigrng = uu____14151;
              FStar_Syntax_Syntax.sigquals = uu____14152;
              FStar_Syntax_Syntax.sigmeta = uu____14153;
              FStar_Syntax_Syntax.sigattrs = uu____14154;_},uu____14155),uu____14156)
          -> l
      | uu____14211 ->
          let uu____14212 =
            let uu____14213 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____14213  in
          failwith uu____14212
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14262)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____14313,lbs),uu____14315)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____14337 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____14337
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____14369 -> FStar_Pervasives_Native.None)
        | uu____14374 -> FStar_Pervasives_Native.None
  
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
        let uu____14404 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____14404
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14429),uu____14430) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____14479 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14500 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____14500
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____14519 = lookup_qname env ftv  in
      match uu____14519 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14523) ->
          let uu____14568 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14568 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14589,t),r) ->
               let uu____14604 =
                 let uu____14605 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14605 t  in
               FStar_Pervasives_Native.Some uu____14604)
      | uu____14606 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14617 = try_lookup_effect_lid env ftv  in
      match uu____14617 with
      | FStar_Pervasives_Native.None  ->
          let uu____14620 = name_not_found ftv  in
          let uu____14625 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14620 uu____14625
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
        let uu____14648 = lookup_qname env lid0  in
        match uu____14648 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14659);
                FStar_Syntax_Syntax.sigrng = uu____14660;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14662;
                FStar_Syntax_Syntax.sigattrs = uu____14663;_},FStar_Pervasives_Native.None
              ),uu____14664)
            ->
            let lid1 =
              let uu____14718 =
                let uu____14719 = FStar_Ident.range_of_lid lid  in
                let uu____14720 =
                  let uu____14721 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14721  in
                FStar_Range.set_use_range uu____14719 uu____14720  in
              FStar_Ident.set_lid_range lid uu____14718  in
            let uu____14722 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___225_14726  ->
                      match uu___225_14726 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14727 -> false))
               in
            if uu____14722
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14741 =
                      let uu____14742 =
                        let uu____14743 = get_range env  in
                        FStar_Range.string_of_range uu____14743  in
                      let uu____14744 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14745 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14742 uu____14744 uu____14745
                       in
                    failwith uu____14741)
                  in
               match (binders, univs1) with
               | ([],uu____14762) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14787,uu____14788::uu____14789::uu____14790) ->
                   let uu____14811 =
                     let uu____14812 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14813 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14812 uu____14813
                      in
                   failwith uu____14811
               | uu____14820 ->
                   let uu____14835 =
                     let uu____14840 =
                       let uu____14841 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14841)  in
                     inst_tscheme_with uu____14840 insts  in
                   (match uu____14835 with
                    | (uu____14854,t) ->
                        let t1 =
                          let uu____14857 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14857 t  in
                        let uu____14858 =
                          let uu____14859 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14859.FStar_Syntax_Syntax.n  in
                        (match uu____14858 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14894 -> failwith "Impossible")))
        | uu____14901 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14924 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14924 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14937,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14944 = find1 l2  in
            (match uu____14944 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14951 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14951 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14955 = find1 l  in
            (match uu____14955 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14960 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14960
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14974 = lookup_qname env l1  in
      match uu____14974 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14977;
              FStar_Syntax_Syntax.sigrng = uu____14978;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14980;
              FStar_Syntax_Syntax.sigattrs = uu____14981;_},uu____14982),uu____14983)
          -> q
      | uu____15034 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____15055 =
          let uu____15056 =
            let uu____15057 = FStar_Util.string_of_int i  in
            let uu____15058 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____15057 uu____15058
             in
          failwith uu____15056  in
        let uu____15059 = lookup_datacon env lid  in
        match uu____15059 with
        | (uu____15064,t) ->
            let uu____15066 =
              let uu____15067 = FStar_Syntax_Subst.compress t  in
              uu____15067.FStar_Syntax_Syntax.n  in
            (match uu____15066 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15071) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____15112 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____15112
                      FStar_Pervasives_Native.fst)
             | uu____15123 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15134 = lookup_qname env l  in
      match uu____15134 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15135,uu____15136,uu____15137);
              FStar_Syntax_Syntax.sigrng = uu____15138;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15140;
              FStar_Syntax_Syntax.sigattrs = uu____15141;_},uu____15142),uu____15143)
          ->
          FStar_Util.for_some
            (fun uu___226_15196  ->
               match uu___226_15196 with
               | FStar_Syntax_Syntax.Projector uu____15197 -> true
               | uu____15202 -> false) quals
      | uu____15203 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15214 = lookup_qname env lid  in
      match uu____15214 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15215,uu____15216,uu____15217,uu____15218,uu____15219,uu____15220);
              FStar_Syntax_Syntax.sigrng = uu____15221;
              FStar_Syntax_Syntax.sigquals = uu____15222;
              FStar_Syntax_Syntax.sigmeta = uu____15223;
              FStar_Syntax_Syntax.sigattrs = uu____15224;_},uu____15225),uu____15226)
          -> true
      | uu____15281 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15292 = lookup_qname env lid  in
      match uu____15292 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15293,uu____15294,uu____15295,uu____15296,uu____15297,uu____15298);
              FStar_Syntax_Syntax.sigrng = uu____15299;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15301;
              FStar_Syntax_Syntax.sigattrs = uu____15302;_},uu____15303),uu____15304)
          ->
          FStar_Util.for_some
            (fun uu___227_15365  ->
               match uu___227_15365 with
               | FStar_Syntax_Syntax.RecordType uu____15366 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____15375 -> true
               | uu____15384 -> false) quals
      | uu____15385 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____15391,uu____15392);
            FStar_Syntax_Syntax.sigrng = uu____15393;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____15395;
            FStar_Syntax_Syntax.sigattrs = uu____15396;_},uu____15397),uu____15398)
        ->
        FStar_Util.for_some
          (fun uu___228_15455  ->
             match uu___228_15455 with
             | FStar_Syntax_Syntax.Action uu____15456 -> true
             | uu____15457 -> false) quals
    | uu____15458 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15469 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____15469
  
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
      let uu____15483 =
        let uu____15484 = FStar_Syntax_Util.un_uinst head1  in
        uu____15484.FStar_Syntax_Syntax.n  in
      match uu____15483 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____15488 ->
               true
           | uu____15489 -> false)
      | uu____15490 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15501 = lookup_qname env l  in
      match uu____15501 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____15503),uu____15504) ->
          FStar_Util.for_some
            (fun uu___229_15552  ->
               match uu___229_15552 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____15553 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____15554 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15625 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15641) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15658 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15665 ->
                 FStar_Pervasives_Native.Some true
             | uu____15682 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15683 =
        let uu____15686 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15686 mapper  in
      match uu____15683 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15736 = lookup_qname env lid  in
      match uu____15736 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15737,uu____15738,tps,uu____15740,uu____15741,uu____15742);
              FStar_Syntax_Syntax.sigrng = uu____15743;
              FStar_Syntax_Syntax.sigquals = uu____15744;
              FStar_Syntax_Syntax.sigmeta = uu____15745;
              FStar_Syntax_Syntax.sigattrs = uu____15746;_},uu____15747),uu____15748)
          -> FStar_List.length tps
      | uu____15813 ->
          let uu____15814 = name_not_found lid  in
          let uu____15819 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15814 uu____15819
  
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
           (fun uu____15863  ->
              match uu____15863 with
              | (d,uu____15871) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15886 = effect_decl_opt env l  in
      match uu____15886 with
      | FStar_Pervasives_Native.None  ->
          let uu____15901 = name_not_found l  in
          let uu____15906 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15901 uu____15906
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15928  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15947  ->
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
        let uu____15978 = FStar_Ident.lid_equals l1 l2  in
        if uu____15978
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15986 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15986
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15994 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____16047  ->
                        match uu____16047 with
                        | (m1,m2,uu____16060,uu____16061,uu____16062) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15994 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16079 =
                    let uu____16084 =
                      let uu____16085 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____16086 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____16085
                        uu____16086
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____16084)
                     in
                  FStar_Errors.raise_error uu____16079 env.range
              | FStar_Pervasives_Native.Some
                  (uu____16093,uu____16094,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____16127 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____16127
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
  'Auu____16143 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____16143)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____16172 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____16198  ->
                match uu____16198 with
                | (d,uu____16204) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____16172 with
      | FStar_Pervasives_Native.None  ->
          let uu____16215 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____16215
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____16228 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____16228 with
           | (uu____16243,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____16261)::(wp,uu____16263)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____16319 -> failwith "Impossible"))
  
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
          let uu____16374 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____16374
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____16376 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____16376
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
                  let uu____16384 = get_range env  in
                  let uu____16385 =
                    let uu____16392 =
                      let uu____16393 =
                        let uu____16410 =
                          let uu____16421 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____16421]  in
                        (null_wp, uu____16410)  in
                      FStar_Syntax_Syntax.Tm_app uu____16393  in
                    FStar_Syntax_Syntax.mk uu____16392  in
                  uu____16385 FStar_Pervasives_Native.None uu____16384  in
                let uu____16461 =
                  let uu____16462 =
                    let uu____16473 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____16473]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____16462;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____16461))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___244_16510 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___244_16510.order);
              joins = (uu___244_16510.joins)
            }  in
          let uu___245_16519 = env  in
          {
            solver = (uu___245_16519.solver);
            range = (uu___245_16519.range);
            curmodule = (uu___245_16519.curmodule);
            gamma = (uu___245_16519.gamma);
            gamma_sig = (uu___245_16519.gamma_sig);
            gamma_cache = (uu___245_16519.gamma_cache);
            modules = (uu___245_16519.modules);
            expected_typ = (uu___245_16519.expected_typ);
            sigtab = (uu___245_16519.sigtab);
            attrtab = (uu___245_16519.attrtab);
            is_pattern = (uu___245_16519.is_pattern);
            instantiate_imp = (uu___245_16519.instantiate_imp);
            effects;
            generalize = (uu___245_16519.generalize);
            letrecs = (uu___245_16519.letrecs);
            top_level = (uu___245_16519.top_level);
            check_uvars = (uu___245_16519.check_uvars);
            use_eq = (uu___245_16519.use_eq);
            is_iface = (uu___245_16519.is_iface);
            admit = (uu___245_16519.admit);
            lax = (uu___245_16519.lax);
            lax_universes = (uu___245_16519.lax_universes);
            phase1 = (uu___245_16519.phase1);
            failhard = (uu___245_16519.failhard);
            nosynth = (uu___245_16519.nosynth);
            uvar_subtyping = (uu___245_16519.uvar_subtyping);
            tc_term = (uu___245_16519.tc_term);
            type_of = (uu___245_16519.type_of);
            universe_of = (uu___245_16519.universe_of);
            check_type_of = (uu___245_16519.check_type_of);
            use_bv_sorts = (uu___245_16519.use_bv_sorts);
            qtbl_name_and_index = (uu___245_16519.qtbl_name_and_index);
            normalized_eff_names = (uu___245_16519.normalized_eff_names);
            proof_ns = (uu___245_16519.proof_ns);
            synth_hook = (uu___245_16519.synth_hook);
            splice = (uu___245_16519.splice);
            is_native_tactic = (uu___245_16519.is_native_tactic);
            identifier_info = (uu___245_16519.identifier_info);
            tc_hooks = (uu___245_16519.tc_hooks);
            dsenv = (uu___245_16519.dsenv);
            dep_graph = (uu___245_16519.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____16549 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____16549  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16707 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16708 = l1 u t wp e  in
                                l2 u t uu____16707 uu____16708))
                | uu____16709 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16781 = inst_tscheme_with lift_t [u]  in
            match uu____16781 with
            | (uu____16788,lift_t1) ->
                let uu____16790 =
                  let uu____16797 =
                    let uu____16798 =
                      let uu____16815 =
                        let uu____16826 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16835 =
                          let uu____16846 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16846]  in
                        uu____16826 :: uu____16835  in
                      (lift_t1, uu____16815)  in
                    FStar_Syntax_Syntax.Tm_app uu____16798  in
                  FStar_Syntax_Syntax.mk uu____16797  in
                uu____16790 FStar_Pervasives_Native.None
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
            let uu____16958 = inst_tscheme_with lift_t [u]  in
            match uu____16958 with
            | (uu____16965,lift_t1) ->
                let uu____16967 =
                  let uu____16974 =
                    let uu____16975 =
                      let uu____16992 =
                        let uu____17003 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17012 =
                          let uu____17023 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____17032 =
                            let uu____17043 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____17043]  in
                          uu____17023 :: uu____17032  in
                        uu____17003 :: uu____17012  in
                      (lift_t1, uu____16992)  in
                    FStar_Syntax_Syntax.Tm_app uu____16975  in
                  FStar_Syntax_Syntax.mk uu____16974  in
                uu____16967 FStar_Pervasives_Native.None
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
              let uu____17145 =
                let uu____17146 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____17146
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____17145  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____17150 =
              let uu____17151 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____17151  in
            let uu____17152 =
              let uu____17153 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____17179 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____17179)
                 in
              FStar_Util.dflt "none" uu____17153  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____17150
              uu____17152
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____17205  ->
                    match uu____17205 with
                    | (e,uu____17213) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____17236 =
            match uu____17236 with
            | (i,j) ->
                let uu____17247 = FStar_Ident.lid_equals i j  in
                if uu____17247
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
              let uu____17279 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____17289 = FStar_Ident.lid_equals i k  in
                        if uu____17289
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____17300 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____17300
                                  then []
                                  else
                                    (let uu____17304 =
                                       let uu____17313 =
                                         find_edge order1 (i, k)  in
                                       let uu____17316 =
                                         find_edge order1 (k, j)  in
                                       (uu____17313, uu____17316)  in
                                     match uu____17304 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____17331 =
                                           compose_edges e1 e2  in
                                         [uu____17331]
                                     | uu____17332 -> [])))))
                 in
              FStar_List.append order1 uu____17279  in
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
                   let uu____17362 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____17364 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____17364
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____17362
                   then
                     let uu____17369 =
                       let uu____17374 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____17374)
                        in
                     let uu____17375 = get_range env  in
                     FStar_Errors.raise_error uu____17369 uu____17375
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____17452 = FStar_Ident.lid_equals i j
                                   in
                                if uu____17452
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____17501 =
                                              let uu____17510 =
                                                find_edge order2 (i, k)  in
                                              let uu____17513 =
                                                find_edge order2 (j, k)  in
                                              (uu____17510, uu____17513)  in
                                            match uu____17501 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____17555,uu____17556)
                                                     ->
                                                     let uu____17563 =
                                                       let uu____17568 =
                                                         let uu____17569 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17569
                                                          in
                                                       let uu____17572 =
                                                         let uu____17573 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17573
                                                          in
                                                       (uu____17568,
                                                         uu____17572)
                                                        in
                                                     (match uu____17563 with
                                                      | (true ,true ) ->
                                                          let uu____17584 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____17584
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
                                            | uu____17609 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___246_17682 = env.effects  in
              { decls = (uu___246_17682.decls); order = order2; joins }  in
            let uu___247_17683 = env  in
            {
              solver = (uu___247_17683.solver);
              range = (uu___247_17683.range);
              curmodule = (uu___247_17683.curmodule);
              gamma = (uu___247_17683.gamma);
              gamma_sig = (uu___247_17683.gamma_sig);
              gamma_cache = (uu___247_17683.gamma_cache);
              modules = (uu___247_17683.modules);
              expected_typ = (uu___247_17683.expected_typ);
              sigtab = (uu___247_17683.sigtab);
              attrtab = (uu___247_17683.attrtab);
              is_pattern = (uu___247_17683.is_pattern);
              instantiate_imp = (uu___247_17683.instantiate_imp);
              effects;
              generalize = (uu___247_17683.generalize);
              letrecs = (uu___247_17683.letrecs);
              top_level = (uu___247_17683.top_level);
              check_uvars = (uu___247_17683.check_uvars);
              use_eq = (uu___247_17683.use_eq);
              is_iface = (uu___247_17683.is_iface);
              admit = (uu___247_17683.admit);
              lax = (uu___247_17683.lax);
              lax_universes = (uu___247_17683.lax_universes);
              phase1 = (uu___247_17683.phase1);
              failhard = (uu___247_17683.failhard);
              nosynth = (uu___247_17683.nosynth);
              uvar_subtyping = (uu___247_17683.uvar_subtyping);
              tc_term = (uu___247_17683.tc_term);
              type_of = (uu___247_17683.type_of);
              universe_of = (uu___247_17683.universe_of);
              check_type_of = (uu___247_17683.check_type_of);
              use_bv_sorts = (uu___247_17683.use_bv_sorts);
              qtbl_name_and_index = (uu___247_17683.qtbl_name_and_index);
              normalized_eff_names = (uu___247_17683.normalized_eff_names);
              proof_ns = (uu___247_17683.proof_ns);
              synth_hook = (uu___247_17683.synth_hook);
              splice = (uu___247_17683.splice);
              is_native_tactic = (uu___247_17683.is_native_tactic);
              identifier_info = (uu___247_17683.identifier_info);
              tc_hooks = (uu___247_17683.tc_hooks);
              dsenv = (uu___247_17683.dsenv);
              dep_graph = (uu___247_17683.dep_graph)
            }))
      | uu____17684 -> env
  
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
        | uu____17712 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17724 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17724 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17741 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17741 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17763 =
                     let uu____17768 =
                       let uu____17769 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17776 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17785 =
                         let uu____17786 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17786  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17769 uu____17776 uu____17785
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17768)
                      in
                   FStar_Errors.raise_error uu____17763
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17791 =
                     let uu____17802 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17802 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17839  ->
                        fun uu____17840  ->
                          match (uu____17839, uu____17840) with
                          | ((x,uu____17870),(t,uu____17872)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17791
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____17903 =
                     let uu___248_17904 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___248_17904.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___248_17904.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___248_17904.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___248_17904.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____17903
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
          let uu____17934 = effect_decl_opt env effect_name  in
          match uu____17934 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17967 =
                only_reifiable &&
                  (let uu____17969 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17969)
                 in
              if uu____17967
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17985 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____18008 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____18045 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____18045
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____18046 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____18046
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____18060 =
                       let uu____18063 = get_range env  in
                       let uu____18064 =
                         let uu____18071 =
                           let uu____18072 =
                             let uu____18089 =
                               let uu____18100 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____18100; wp]  in
                             (repr, uu____18089)  in
                           FStar_Syntax_Syntax.Tm_app uu____18072  in
                         FStar_Syntax_Syntax.mk uu____18071  in
                       uu____18064 FStar_Pervasives_Native.None uu____18063
                        in
                     FStar_Pervasives_Native.Some uu____18060)
  
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
          let uu____18190 =
            let uu____18195 =
              let uu____18196 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____18196
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____18195)  in
          let uu____18197 = get_range env  in
          FStar_Errors.raise_error uu____18190 uu____18197  in
        let uu____18198 = effect_repr_aux true env c u_c  in
        match uu____18198 with
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
      | uu____18244 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____18255 =
        let uu____18256 = FStar_Syntax_Subst.compress t  in
        uu____18256.FStar_Syntax_Syntax.n  in
      match uu____18255 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____18259,c) ->
          is_reifiable_comp env c
      | uu____18281 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___249_18302 = env  in
        {
          solver = (uu___249_18302.solver);
          range = (uu___249_18302.range);
          curmodule = (uu___249_18302.curmodule);
          gamma = (uu___249_18302.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___249_18302.gamma_cache);
          modules = (uu___249_18302.modules);
          expected_typ = (uu___249_18302.expected_typ);
          sigtab = (uu___249_18302.sigtab);
          attrtab = (uu___249_18302.attrtab);
          is_pattern = (uu___249_18302.is_pattern);
          instantiate_imp = (uu___249_18302.instantiate_imp);
          effects = (uu___249_18302.effects);
          generalize = (uu___249_18302.generalize);
          letrecs = (uu___249_18302.letrecs);
          top_level = (uu___249_18302.top_level);
          check_uvars = (uu___249_18302.check_uvars);
          use_eq = (uu___249_18302.use_eq);
          is_iface = (uu___249_18302.is_iface);
          admit = (uu___249_18302.admit);
          lax = (uu___249_18302.lax);
          lax_universes = (uu___249_18302.lax_universes);
          phase1 = (uu___249_18302.phase1);
          failhard = (uu___249_18302.failhard);
          nosynth = (uu___249_18302.nosynth);
          uvar_subtyping = (uu___249_18302.uvar_subtyping);
          tc_term = (uu___249_18302.tc_term);
          type_of = (uu___249_18302.type_of);
          universe_of = (uu___249_18302.universe_of);
          check_type_of = (uu___249_18302.check_type_of);
          use_bv_sorts = (uu___249_18302.use_bv_sorts);
          qtbl_name_and_index = (uu___249_18302.qtbl_name_and_index);
          normalized_eff_names = (uu___249_18302.normalized_eff_names);
          proof_ns = (uu___249_18302.proof_ns);
          synth_hook = (uu___249_18302.synth_hook);
          splice = (uu___249_18302.splice);
          is_native_tactic = (uu___249_18302.is_native_tactic);
          identifier_info = (uu___249_18302.identifier_info);
          tc_hooks = (uu___249_18302.tc_hooks);
          dsenv = (uu___249_18302.dsenv);
          dep_graph = (uu___249_18302.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___250_18314 = env  in
      {
        solver = (uu___250_18314.solver);
        range = (uu___250_18314.range);
        curmodule = (uu___250_18314.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___250_18314.gamma_sig);
        gamma_cache = (uu___250_18314.gamma_cache);
        modules = (uu___250_18314.modules);
        expected_typ = (uu___250_18314.expected_typ);
        sigtab = (uu___250_18314.sigtab);
        attrtab = (uu___250_18314.attrtab);
        is_pattern = (uu___250_18314.is_pattern);
        instantiate_imp = (uu___250_18314.instantiate_imp);
        effects = (uu___250_18314.effects);
        generalize = (uu___250_18314.generalize);
        letrecs = (uu___250_18314.letrecs);
        top_level = (uu___250_18314.top_level);
        check_uvars = (uu___250_18314.check_uvars);
        use_eq = (uu___250_18314.use_eq);
        is_iface = (uu___250_18314.is_iface);
        admit = (uu___250_18314.admit);
        lax = (uu___250_18314.lax);
        lax_universes = (uu___250_18314.lax_universes);
        phase1 = (uu___250_18314.phase1);
        failhard = (uu___250_18314.failhard);
        nosynth = (uu___250_18314.nosynth);
        uvar_subtyping = (uu___250_18314.uvar_subtyping);
        tc_term = (uu___250_18314.tc_term);
        type_of = (uu___250_18314.type_of);
        universe_of = (uu___250_18314.universe_of);
        check_type_of = (uu___250_18314.check_type_of);
        use_bv_sorts = (uu___250_18314.use_bv_sorts);
        qtbl_name_and_index = (uu___250_18314.qtbl_name_and_index);
        normalized_eff_names = (uu___250_18314.normalized_eff_names);
        proof_ns = (uu___250_18314.proof_ns);
        synth_hook = (uu___250_18314.synth_hook);
        splice = (uu___250_18314.splice);
        is_native_tactic = (uu___250_18314.is_native_tactic);
        identifier_info = (uu___250_18314.identifier_info);
        tc_hooks = (uu___250_18314.tc_hooks);
        dsenv = (uu___250_18314.dsenv);
        dep_graph = (uu___250_18314.dep_graph)
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
            (let uu___251_18369 = env  in
             {
               solver = (uu___251_18369.solver);
               range = (uu___251_18369.range);
               curmodule = (uu___251_18369.curmodule);
               gamma = rest;
               gamma_sig = (uu___251_18369.gamma_sig);
               gamma_cache = (uu___251_18369.gamma_cache);
               modules = (uu___251_18369.modules);
               expected_typ = (uu___251_18369.expected_typ);
               sigtab = (uu___251_18369.sigtab);
               attrtab = (uu___251_18369.attrtab);
               is_pattern = (uu___251_18369.is_pattern);
               instantiate_imp = (uu___251_18369.instantiate_imp);
               effects = (uu___251_18369.effects);
               generalize = (uu___251_18369.generalize);
               letrecs = (uu___251_18369.letrecs);
               top_level = (uu___251_18369.top_level);
               check_uvars = (uu___251_18369.check_uvars);
               use_eq = (uu___251_18369.use_eq);
               is_iface = (uu___251_18369.is_iface);
               admit = (uu___251_18369.admit);
               lax = (uu___251_18369.lax);
               lax_universes = (uu___251_18369.lax_universes);
               phase1 = (uu___251_18369.phase1);
               failhard = (uu___251_18369.failhard);
               nosynth = (uu___251_18369.nosynth);
               uvar_subtyping = (uu___251_18369.uvar_subtyping);
               tc_term = (uu___251_18369.tc_term);
               type_of = (uu___251_18369.type_of);
               universe_of = (uu___251_18369.universe_of);
               check_type_of = (uu___251_18369.check_type_of);
               use_bv_sorts = (uu___251_18369.use_bv_sorts);
               qtbl_name_and_index = (uu___251_18369.qtbl_name_and_index);
               normalized_eff_names = (uu___251_18369.normalized_eff_names);
               proof_ns = (uu___251_18369.proof_ns);
               synth_hook = (uu___251_18369.synth_hook);
               splice = (uu___251_18369.splice);
               is_native_tactic = (uu___251_18369.is_native_tactic);
               identifier_info = (uu___251_18369.identifier_info);
               tc_hooks = (uu___251_18369.tc_hooks);
               dsenv = (uu___251_18369.dsenv);
               dep_graph = (uu___251_18369.dep_graph)
             }))
    | uu____18370 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____18398  ->
             match uu____18398 with | (x,uu____18406) -> push_bv env1 x) env
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
            let uu___252_18440 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___252_18440.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___252_18440.FStar_Syntax_Syntax.index);
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
      (let uu___253_18480 = env  in
       {
         solver = (uu___253_18480.solver);
         range = (uu___253_18480.range);
         curmodule = (uu___253_18480.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___253_18480.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___253_18480.sigtab);
         attrtab = (uu___253_18480.attrtab);
         is_pattern = (uu___253_18480.is_pattern);
         instantiate_imp = (uu___253_18480.instantiate_imp);
         effects = (uu___253_18480.effects);
         generalize = (uu___253_18480.generalize);
         letrecs = (uu___253_18480.letrecs);
         top_level = (uu___253_18480.top_level);
         check_uvars = (uu___253_18480.check_uvars);
         use_eq = (uu___253_18480.use_eq);
         is_iface = (uu___253_18480.is_iface);
         admit = (uu___253_18480.admit);
         lax = (uu___253_18480.lax);
         lax_universes = (uu___253_18480.lax_universes);
         phase1 = (uu___253_18480.phase1);
         failhard = (uu___253_18480.failhard);
         nosynth = (uu___253_18480.nosynth);
         uvar_subtyping = (uu___253_18480.uvar_subtyping);
         tc_term = (uu___253_18480.tc_term);
         type_of = (uu___253_18480.type_of);
         universe_of = (uu___253_18480.universe_of);
         check_type_of = (uu___253_18480.check_type_of);
         use_bv_sorts = (uu___253_18480.use_bv_sorts);
         qtbl_name_and_index = (uu___253_18480.qtbl_name_and_index);
         normalized_eff_names = (uu___253_18480.normalized_eff_names);
         proof_ns = (uu___253_18480.proof_ns);
         synth_hook = (uu___253_18480.synth_hook);
         splice = (uu___253_18480.splice);
         is_native_tactic = (uu___253_18480.is_native_tactic);
         identifier_info = (uu___253_18480.identifier_info);
         tc_hooks = (uu___253_18480.tc_hooks);
         dsenv = (uu___253_18480.dsenv);
         dep_graph = (uu___253_18480.dep_graph)
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
        let uu____18522 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____18522 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____18550 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____18550)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___254_18565 = env  in
      {
        solver = (uu___254_18565.solver);
        range = (uu___254_18565.range);
        curmodule = (uu___254_18565.curmodule);
        gamma = (uu___254_18565.gamma);
        gamma_sig = (uu___254_18565.gamma_sig);
        gamma_cache = (uu___254_18565.gamma_cache);
        modules = (uu___254_18565.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___254_18565.sigtab);
        attrtab = (uu___254_18565.attrtab);
        is_pattern = (uu___254_18565.is_pattern);
        instantiate_imp = (uu___254_18565.instantiate_imp);
        effects = (uu___254_18565.effects);
        generalize = (uu___254_18565.generalize);
        letrecs = (uu___254_18565.letrecs);
        top_level = (uu___254_18565.top_level);
        check_uvars = (uu___254_18565.check_uvars);
        use_eq = false;
        is_iface = (uu___254_18565.is_iface);
        admit = (uu___254_18565.admit);
        lax = (uu___254_18565.lax);
        lax_universes = (uu___254_18565.lax_universes);
        phase1 = (uu___254_18565.phase1);
        failhard = (uu___254_18565.failhard);
        nosynth = (uu___254_18565.nosynth);
        uvar_subtyping = (uu___254_18565.uvar_subtyping);
        tc_term = (uu___254_18565.tc_term);
        type_of = (uu___254_18565.type_of);
        universe_of = (uu___254_18565.universe_of);
        check_type_of = (uu___254_18565.check_type_of);
        use_bv_sorts = (uu___254_18565.use_bv_sorts);
        qtbl_name_and_index = (uu___254_18565.qtbl_name_and_index);
        normalized_eff_names = (uu___254_18565.normalized_eff_names);
        proof_ns = (uu___254_18565.proof_ns);
        synth_hook = (uu___254_18565.synth_hook);
        splice = (uu___254_18565.splice);
        is_native_tactic = (uu___254_18565.is_native_tactic);
        identifier_info = (uu___254_18565.identifier_info);
        tc_hooks = (uu___254_18565.tc_hooks);
        dsenv = (uu___254_18565.dsenv);
        dep_graph = (uu___254_18565.dep_graph)
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
    let uu____18593 = expected_typ env_  in
    ((let uu___255_18599 = env_  in
      {
        solver = (uu___255_18599.solver);
        range = (uu___255_18599.range);
        curmodule = (uu___255_18599.curmodule);
        gamma = (uu___255_18599.gamma);
        gamma_sig = (uu___255_18599.gamma_sig);
        gamma_cache = (uu___255_18599.gamma_cache);
        modules = (uu___255_18599.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___255_18599.sigtab);
        attrtab = (uu___255_18599.attrtab);
        is_pattern = (uu___255_18599.is_pattern);
        instantiate_imp = (uu___255_18599.instantiate_imp);
        effects = (uu___255_18599.effects);
        generalize = (uu___255_18599.generalize);
        letrecs = (uu___255_18599.letrecs);
        top_level = (uu___255_18599.top_level);
        check_uvars = (uu___255_18599.check_uvars);
        use_eq = false;
        is_iface = (uu___255_18599.is_iface);
        admit = (uu___255_18599.admit);
        lax = (uu___255_18599.lax);
        lax_universes = (uu___255_18599.lax_universes);
        phase1 = (uu___255_18599.phase1);
        failhard = (uu___255_18599.failhard);
        nosynth = (uu___255_18599.nosynth);
        uvar_subtyping = (uu___255_18599.uvar_subtyping);
        tc_term = (uu___255_18599.tc_term);
        type_of = (uu___255_18599.type_of);
        universe_of = (uu___255_18599.universe_of);
        check_type_of = (uu___255_18599.check_type_of);
        use_bv_sorts = (uu___255_18599.use_bv_sorts);
        qtbl_name_and_index = (uu___255_18599.qtbl_name_and_index);
        normalized_eff_names = (uu___255_18599.normalized_eff_names);
        proof_ns = (uu___255_18599.proof_ns);
        synth_hook = (uu___255_18599.synth_hook);
        splice = (uu___255_18599.splice);
        is_native_tactic = (uu___255_18599.is_native_tactic);
        identifier_info = (uu___255_18599.identifier_info);
        tc_hooks = (uu___255_18599.tc_hooks);
        dsenv = (uu___255_18599.dsenv);
        dep_graph = (uu___255_18599.dep_graph)
      }), uu____18593)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____18609 =
      let uu____18612 = FStar_Ident.id_of_text ""  in [uu____18612]  in
    FStar_Ident.lid_of_ids uu____18609  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____18618 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____18618
        then
          let uu____18621 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____18621 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___256_18648 = env  in
       {
         solver = (uu___256_18648.solver);
         range = (uu___256_18648.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___256_18648.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___256_18648.expected_typ);
         sigtab = (uu___256_18648.sigtab);
         attrtab = (uu___256_18648.attrtab);
         is_pattern = (uu___256_18648.is_pattern);
         instantiate_imp = (uu___256_18648.instantiate_imp);
         effects = (uu___256_18648.effects);
         generalize = (uu___256_18648.generalize);
         letrecs = (uu___256_18648.letrecs);
         top_level = (uu___256_18648.top_level);
         check_uvars = (uu___256_18648.check_uvars);
         use_eq = (uu___256_18648.use_eq);
         is_iface = (uu___256_18648.is_iface);
         admit = (uu___256_18648.admit);
         lax = (uu___256_18648.lax);
         lax_universes = (uu___256_18648.lax_universes);
         phase1 = (uu___256_18648.phase1);
         failhard = (uu___256_18648.failhard);
         nosynth = (uu___256_18648.nosynth);
         uvar_subtyping = (uu___256_18648.uvar_subtyping);
         tc_term = (uu___256_18648.tc_term);
         type_of = (uu___256_18648.type_of);
         universe_of = (uu___256_18648.universe_of);
         check_type_of = (uu___256_18648.check_type_of);
         use_bv_sorts = (uu___256_18648.use_bv_sorts);
         qtbl_name_and_index = (uu___256_18648.qtbl_name_and_index);
         normalized_eff_names = (uu___256_18648.normalized_eff_names);
         proof_ns = (uu___256_18648.proof_ns);
         synth_hook = (uu___256_18648.synth_hook);
         splice = (uu___256_18648.splice);
         is_native_tactic = (uu___256_18648.is_native_tactic);
         identifier_info = (uu___256_18648.identifier_info);
         tc_hooks = (uu___256_18648.tc_hooks);
         dsenv = (uu___256_18648.dsenv);
         dep_graph = (uu___256_18648.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18699)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18703,(uu____18704,t)))::tl1
          ->
          let uu____18725 =
            let uu____18728 = FStar_Syntax_Free.uvars t  in
            ext out uu____18728  in
          aux uu____18725 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18731;
            FStar_Syntax_Syntax.index = uu____18732;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18739 =
            let uu____18742 = FStar_Syntax_Free.uvars t  in
            ext out uu____18742  in
          aux uu____18739 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18799)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18803,(uu____18804,t)))::tl1
          ->
          let uu____18825 =
            let uu____18828 = FStar_Syntax_Free.univs t  in
            ext out uu____18828  in
          aux uu____18825 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18831;
            FStar_Syntax_Syntax.index = uu____18832;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18839 =
            let uu____18842 = FStar_Syntax_Free.univs t  in
            ext out uu____18842  in
          aux uu____18839 tl1
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
          let uu____18903 = FStar_Util.set_add uname out  in
          aux uu____18903 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18906,(uu____18907,t)))::tl1
          ->
          let uu____18928 =
            let uu____18931 = FStar_Syntax_Free.univnames t  in
            ext out uu____18931  in
          aux uu____18928 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18934;
            FStar_Syntax_Syntax.index = uu____18935;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18942 =
            let uu____18945 = FStar_Syntax_Free.univnames t  in
            ext out uu____18945  in
          aux uu____18942 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___230_18965  ->
            match uu___230_18965 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18969 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____18982 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____18992 =
      let uu____19001 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____19001
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____18992 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____19045 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___231_19055  ->
              match uu___231_19055 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____19057 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____19057
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____19060) ->
                  let uu____19077 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____19077))
       in
    FStar_All.pipe_right uu____19045 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___232_19084  ->
    match uu___232_19084 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____19086 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____19086
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____19106  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____19148) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____19167,uu____19168) -> false  in
      let uu____19177 =
        FStar_List.tryFind
          (fun uu____19195  ->
             match uu____19195 with | (p,uu____19203) -> list_prefix p path)
          env.proof_ns
         in
      match uu____19177 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____19214,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19236 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____19236
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___257_19254 = e  in
        {
          solver = (uu___257_19254.solver);
          range = (uu___257_19254.range);
          curmodule = (uu___257_19254.curmodule);
          gamma = (uu___257_19254.gamma);
          gamma_sig = (uu___257_19254.gamma_sig);
          gamma_cache = (uu___257_19254.gamma_cache);
          modules = (uu___257_19254.modules);
          expected_typ = (uu___257_19254.expected_typ);
          sigtab = (uu___257_19254.sigtab);
          attrtab = (uu___257_19254.attrtab);
          is_pattern = (uu___257_19254.is_pattern);
          instantiate_imp = (uu___257_19254.instantiate_imp);
          effects = (uu___257_19254.effects);
          generalize = (uu___257_19254.generalize);
          letrecs = (uu___257_19254.letrecs);
          top_level = (uu___257_19254.top_level);
          check_uvars = (uu___257_19254.check_uvars);
          use_eq = (uu___257_19254.use_eq);
          is_iface = (uu___257_19254.is_iface);
          admit = (uu___257_19254.admit);
          lax = (uu___257_19254.lax);
          lax_universes = (uu___257_19254.lax_universes);
          phase1 = (uu___257_19254.phase1);
          failhard = (uu___257_19254.failhard);
          nosynth = (uu___257_19254.nosynth);
          uvar_subtyping = (uu___257_19254.uvar_subtyping);
          tc_term = (uu___257_19254.tc_term);
          type_of = (uu___257_19254.type_of);
          universe_of = (uu___257_19254.universe_of);
          check_type_of = (uu___257_19254.check_type_of);
          use_bv_sorts = (uu___257_19254.use_bv_sorts);
          qtbl_name_and_index = (uu___257_19254.qtbl_name_and_index);
          normalized_eff_names = (uu___257_19254.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___257_19254.synth_hook);
          splice = (uu___257_19254.splice);
          is_native_tactic = (uu___257_19254.is_native_tactic);
          identifier_info = (uu___257_19254.identifier_info);
          tc_hooks = (uu___257_19254.tc_hooks);
          dsenv = (uu___257_19254.dsenv);
          dep_graph = (uu___257_19254.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___258_19294 = e  in
      {
        solver = (uu___258_19294.solver);
        range = (uu___258_19294.range);
        curmodule = (uu___258_19294.curmodule);
        gamma = (uu___258_19294.gamma);
        gamma_sig = (uu___258_19294.gamma_sig);
        gamma_cache = (uu___258_19294.gamma_cache);
        modules = (uu___258_19294.modules);
        expected_typ = (uu___258_19294.expected_typ);
        sigtab = (uu___258_19294.sigtab);
        attrtab = (uu___258_19294.attrtab);
        is_pattern = (uu___258_19294.is_pattern);
        instantiate_imp = (uu___258_19294.instantiate_imp);
        effects = (uu___258_19294.effects);
        generalize = (uu___258_19294.generalize);
        letrecs = (uu___258_19294.letrecs);
        top_level = (uu___258_19294.top_level);
        check_uvars = (uu___258_19294.check_uvars);
        use_eq = (uu___258_19294.use_eq);
        is_iface = (uu___258_19294.is_iface);
        admit = (uu___258_19294.admit);
        lax = (uu___258_19294.lax);
        lax_universes = (uu___258_19294.lax_universes);
        phase1 = (uu___258_19294.phase1);
        failhard = (uu___258_19294.failhard);
        nosynth = (uu___258_19294.nosynth);
        uvar_subtyping = (uu___258_19294.uvar_subtyping);
        tc_term = (uu___258_19294.tc_term);
        type_of = (uu___258_19294.type_of);
        universe_of = (uu___258_19294.universe_of);
        check_type_of = (uu___258_19294.check_type_of);
        use_bv_sorts = (uu___258_19294.use_bv_sorts);
        qtbl_name_and_index = (uu___258_19294.qtbl_name_and_index);
        normalized_eff_names = (uu___258_19294.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___258_19294.synth_hook);
        splice = (uu___258_19294.splice);
        is_native_tactic = (uu___258_19294.is_native_tactic);
        identifier_info = (uu___258_19294.identifier_info);
        tc_hooks = (uu___258_19294.tc_hooks);
        dsenv = (uu___258_19294.dsenv);
        dep_graph = (uu___258_19294.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____19309 = FStar_Syntax_Free.names t  in
      let uu____19312 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____19309 uu____19312
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____19333 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____19333
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____19341 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____19341
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____19358 =
      match uu____19358 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____19368 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____19368)
       in
    let uu____19370 =
      let uu____19373 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____19373 FStar_List.rev  in
    FStar_All.pipe_right uu____19370 (FStar_String.concat " ")
  
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
                  (let uu____19426 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____19426 with
                   | FStar_Pervasives_Native.Some uu____19429 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____19430 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____19436;
        univ_ineqs = uu____19437; implicits = uu____19438;_} -> true
    | uu____19449 -> false
  
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
          let uu___259_19476 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___259_19476.deferred);
            univ_ineqs = (uu___259_19476.univ_ineqs);
            implicits = (uu___259_19476.implicits)
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
          let uu____19511 = FStar_Options.defensive ()  in
          if uu____19511
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____19515 =
              let uu____19516 =
                let uu____19517 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____19517  in
              Prims.op_Negation uu____19516  in
            (if uu____19515
             then
               let uu____19522 =
                 let uu____19527 =
                   let uu____19528 = FStar_Syntax_Print.term_to_string t  in
                   let uu____19529 =
                     let uu____19530 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____19530
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____19528 uu____19529
                    in
                 (FStar_Errors.Warning_Defensive, uu____19527)  in
               FStar_Errors.log_issue rng uu____19522
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
          let uu____19561 =
            let uu____19562 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19562  in
          if uu____19561
          then ()
          else
            (let uu____19564 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____19564 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____19587 =
            let uu____19588 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19588  in
          if uu____19587
          then ()
          else
            (let uu____19590 = bound_vars e  in
             def_check_closed_in rng msg uu____19590 t)
  
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
          let uu___260_19625 = g  in
          let uu____19626 =
            let uu____19627 =
              let uu____19628 =
                let uu____19635 =
                  let uu____19636 =
                    let uu____19653 =
                      let uu____19664 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____19664]  in
                    (f, uu____19653)  in
                  FStar_Syntax_Syntax.Tm_app uu____19636  in
                FStar_Syntax_Syntax.mk uu____19635  in
              uu____19628 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____19627
             in
          {
            guard_f = uu____19626;
            deferred = (uu___260_19625.deferred);
            univ_ineqs = (uu___260_19625.univ_ineqs);
            implicits = (uu___260_19625.implicits)
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
          let uu___261_19720 = g  in
          let uu____19721 =
            let uu____19722 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19722  in
          {
            guard_f = uu____19721;
            deferred = (uu___261_19720.deferred);
            univ_ineqs = (uu___261_19720.univ_ineqs);
            implicits = (uu___261_19720.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19728 ->
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
          let uu____19743 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19743
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19749 =
      let uu____19750 = FStar_Syntax_Util.unmeta t  in
      uu____19750.FStar_Syntax_Syntax.n  in
    match uu____19749 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19754 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____19795 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19795;
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
                       let uu____19876 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____19876
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___262_19880 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___262_19880.deferred);
              univ_ineqs = (uu___262_19880.univ_ineqs);
              implicits = (uu___262_19880.implicits)
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
               let uu____19913 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____19913
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
            let uu___263_19936 = g  in
            let uu____19937 =
              let uu____19938 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____19938  in
            {
              guard_f = uu____19937;
              deferred = (uu___263_19936.deferred);
              univ_ineqs = (uu___263_19936.univ_ineqs);
              implicits = (uu___263_19936.implicits)
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
            let uu____19976 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____19976 with
            | FStar_Pervasives_Native.Some
                (uu____20001::(tm,uu____20003)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____20067 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____20085 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____20085;
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
                      imp_range = r;
                      imp_meta = FStar_Pervasives_Native.None
                    }  in
                  let g =
                    let uu___264_20120 = trivial_guard  in
                    {
                      guard_f = (uu___264_20120.guard_f);
                      deferred = (uu___264_20120.deferred);
                      univ_ineqs = (uu___264_20120.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____20137  -> ());
    push = (fun uu____20139  -> ());
    pop = (fun uu____20141  -> ());
    snapshot =
      (fun uu____20143  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____20152  -> fun uu____20153  -> ());
    encode_modul = (fun uu____20164  -> fun uu____20165  -> ());
    encode_sig = (fun uu____20168  -> fun uu____20169  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____20175 =
             let uu____20182 = FStar_Options.peek ()  in (e, g, uu____20182)
              in
           [uu____20175]);
    solve = (fun uu____20198  -> fun uu____20199  -> fun uu____20200  -> ());
    finish = (fun uu____20206  -> ());
    refresh = (fun uu____20208  -> ())
  } 