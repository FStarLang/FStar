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
           (fun uu___220_8876  ->
              match uu___220_8876 with
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
                         let uu___234_8886 = y1  in
                         let uu____8887 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___234_8886.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___234_8886.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8887
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8885
                   | uu____8890 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___235_8902 = env  in
      let uu____8903 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___235_8902.solver);
        range = (uu___235_8902.range);
        curmodule = (uu___235_8902.curmodule);
        gamma = uu____8903;
        gamma_sig = (uu___235_8902.gamma_sig);
        gamma_cache = (uu___235_8902.gamma_cache);
        modules = (uu___235_8902.modules);
        expected_typ = (uu___235_8902.expected_typ);
        sigtab = (uu___235_8902.sigtab);
        attrtab = (uu___235_8902.attrtab);
        is_pattern = (uu___235_8902.is_pattern);
        instantiate_imp = (uu___235_8902.instantiate_imp);
        effects = (uu___235_8902.effects);
        generalize = (uu___235_8902.generalize);
        letrecs = (uu___235_8902.letrecs);
        top_level = (uu___235_8902.top_level);
        check_uvars = (uu___235_8902.check_uvars);
        use_eq = (uu___235_8902.use_eq);
        is_iface = (uu___235_8902.is_iface);
        admit = (uu___235_8902.admit);
        lax = (uu___235_8902.lax);
        lax_universes = (uu___235_8902.lax_universes);
        phase1 = (uu___235_8902.phase1);
        failhard = (uu___235_8902.failhard);
        nosynth = (uu___235_8902.nosynth);
        uvar_subtyping = (uu___235_8902.uvar_subtyping);
        tc_term = (uu___235_8902.tc_term);
        type_of = (uu___235_8902.type_of);
        universe_of = (uu___235_8902.universe_of);
        check_type_of = (uu___235_8902.check_type_of);
        use_bv_sorts = (uu___235_8902.use_bv_sorts);
        qtbl_name_and_index = (uu___235_8902.qtbl_name_and_index);
        normalized_eff_names = (uu___235_8902.normalized_eff_names);
        proof_ns = (uu___235_8902.proof_ns);
        synth_hook = (uu___235_8902.synth_hook);
        splice = (uu___235_8902.splice);
        is_native_tactic = (uu___235_8902.is_native_tactic);
        identifier_info = (uu___235_8902.identifier_info);
        tc_hooks = (uu___235_8902.tc_hooks);
        dsenv = (uu___235_8902.dsenv);
        dep_graph = (uu___235_8902.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8910  -> fun uu____8911  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___236_8931 = env  in
      {
        solver = (uu___236_8931.solver);
        range = (uu___236_8931.range);
        curmodule = (uu___236_8931.curmodule);
        gamma = (uu___236_8931.gamma);
        gamma_sig = (uu___236_8931.gamma_sig);
        gamma_cache = (uu___236_8931.gamma_cache);
        modules = (uu___236_8931.modules);
        expected_typ = (uu___236_8931.expected_typ);
        sigtab = (uu___236_8931.sigtab);
        attrtab = (uu___236_8931.attrtab);
        is_pattern = (uu___236_8931.is_pattern);
        instantiate_imp = (uu___236_8931.instantiate_imp);
        effects = (uu___236_8931.effects);
        generalize = (uu___236_8931.generalize);
        letrecs = (uu___236_8931.letrecs);
        top_level = (uu___236_8931.top_level);
        check_uvars = (uu___236_8931.check_uvars);
        use_eq = (uu___236_8931.use_eq);
        is_iface = (uu___236_8931.is_iface);
        admit = (uu___236_8931.admit);
        lax = (uu___236_8931.lax);
        lax_universes = (uu___236_8931.lax_universes);
        phase1 = (uu___236_8931.phase1);
        failhard = (uu___236_8931.failhard);
        nosynth = (uu___236_8931.nosynth);
        uvar_subtyping = (uu___236_8931.uvar_subtyping);
        tc_term = (uu___236_8931.tc_term);
        type_of = (uu___236_8931.type_of);
        universe_of = (uu___236_8931.universe_of);
        check_type_of = (uu___236_8931.check_type_of);
        use_bv_sorts = (uu___236_8931.use_bv_sorts);
        qtbl_name_and_index = (uu___236_8931.qtbl_name_and_index);
        normalized_eff_names = (uu___236_8931.normalized_eff_names);
        proof_ns = (uu___236_8931.proof_ns);
        synth_hook = (uu___236_8931.synth_hook);
        splice = (uu___236_8931.splice);
        is_native_tactic = (uu___236_8931.is_native_tactic);
        identifier_info = (uu___236_8931.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___236_8931.dsenv);
        dep_graph = (uu___236_8931.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___237_8942 = e  in
      {
        solver = (uu___237_8942.solver);
        range = (uu___237_8942.range);
        curmodule = (uu___237_8942.curmodule);
        gamma = (uu___237_8942.gamma);
        gamma_sig = (uu___237_8942.gamma_sig);
        gamma_cache = (uu___237_8942.gamma_cache);
        modules = (uu___237_8942.modules);
        expected_typ = (uu___237_8942.expected_typ);
        sigtab = (uu___237_8942.sigtab);
        attrtab = (uu___237_8942.attrtab);
        is_pattern = (uu___237_8942.is_pattern);
        instantiate_imp = (uu___237_8942.instantiate_imp);
        effects = (uu___237_8942.effects);
        generalize = (uu___237_8942.generalize);
        letrecs = (uu___237_8942.letrecs);
        top_level = (uu___237_8942.top_level);
        check_uvars = (uu___237_8942.check_uvars);
        use_eq = (uu___237_8942.use_eq);
        is_iface = (uu___237_8942.is_iface);
        admit = (uu___237_8942.admit);
        lax = (uu___237_8942.lax);
        lax_universes = (uu___237_8942.lax_universes);
        phase1 = (uu___237_8942.phase1);
        failhard = (uu___237_8942.failhard);
        nosynth = (uu___237_8942.nosynth);
        uvar_subtyping = (uu___237_8942.uvar_subtyping);
        tc_term = (uu___237_8942.tc_term);
        type_of = (uu___237_8942.type_of);
        universe_of = (uu___237_8942.universe_of);
        check_type_of = (uu___237_8942.check_type_of);
        use_bv_sorts = (uu___237_8942.use_bv_sorts);
        qtbl_name_and_index = (uu___237_8942.qtbl_name_and_index);
        normalized_eff_names = (uu___237_8942.normalized_eff_names);
        proof_ns = (uu___237_8942.proof_ns);
        synth_hook = (uu___237_8942.synth_hook);
        splice = (uu___237_8942.splice);
        is_native_tactic = (uu___237_8942.is_native_tactic);
        identifier_info = (uu___237_8942.identifier_info);
        tc_hooks = (uu___237_8942.tc_hooks);
        dsenv = (uu___237_8942.dsenv);
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
    | uu____9341 ->
        let uu____9350 =
          let uu____9359 =
            let uu____9366 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____9366  in
          let uu____9416 = FStar_ST.op_Bang query_indices  in uu____9359 ::
            uu____9416
           in
        FStar_ST.op_Colon_Equals query_indices uu____9350
  
let (pop_query_indices : unit -> unit) =
  fun uu____9505  ->
    let uu____9506 = FStar_ST.op_Bang query_indices  in
    match uu____9506 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9621  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9651  ->
    match uu____9651 with
    | (l,n1) ->
        let uu____9658 = FStar_ST.op_Bang query_indices  in
        (match uu____9658 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9769 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9788  ->
    let uu____9789 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9789
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9862 =
       let uu____9865 = FStar_ST.op_Bang stack  in env :: uu____9865  in
     FStar_ST.op_Colon_Equals stack uu____9862);
    (let uu___238_9914 = env  in
     let uu____9915 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9918 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9921 = FStar_Util.smap_copy (attrtab env)  in
     let uu____9928 =
       let uu____9941 =
         let uu____9944 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9944  in
       let uu____9969 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9941, uu____9969)  in
     let uu____10010 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____10013 =
       let uu____10016 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____10016  in
     {
       solver = (uu___238_9914.solver);
       range = (uu___238_9914.range);
       curmodule = (uu___238_9914.curmodule);
       gamma = (uu___238_9914.gamma);
       gamma_sig = (uu___238_9914.gamma_sig);
       gamma_cache = uu____9915;
       modules = (uu___238_9914.modules);
       expected_typ = (uu___238_9914.expected_typ);
       sigtab = uu____9918;
       attrtab = uu____9921;
       is_pattern = (uu___238_9914.is_pattern);
       instantiate_imp = (uu___238_9914.instantiate_imp);
       effects = (uu___238_9914.effects);
       generalize = (uu___238_9914.generalize);
       letrecs = (uu___238_9914.letrecs);
       top_level = (uu___238_9914.top_level);
       check_uvars = (uu___238_9914.check_uvars);
       use_eq = (uu___238_9914.use_eq);
       is_iface = (uu___238_9914.is_iface);
       admit = (uu___238_9914.admit);
       lax = (uu___238_9914.lax);
       lax_universes = (uu___238_9914.lax_universes);
       phase1 = (uu___238_9914.phase1);
       failhard = (uu___238_9914.failhard);
       nosynth = (uu___238_9914.nosynth);
       uvar_subtyping = (uu___238_9914.uvar_subtyping);
       tc_term = (uu___238_9914.tc_term);
       type_of = (uu___238_9914.type_of);
       universe_of = (uu___238_9914.universe_of);
       check_type_of = (uu___238_9914.check_type_of);
       use_bv_sorts = (uu___238_9914.use_bv_sorts);
       qtbl_name_and_index = uu____9928;
       normalized_eff_names = uu____10010;
       proof_ns = (uu___238_9914.proof_ns);
       synth_hook = (uu___238_9914.synth_hook);
       splice = (uu___238_9914.splice);
       is_native_tactic = (uu___238_9914.is_native_tactic);
       identifier_info = uu____10013;
       tc_hooks = (uu___238_9914.tc_hooks);
       dsenv = (uu___238_9914.dsenv);
       dep_graph = (uu___238_9914.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____10062  ->
    let uu____10063 = FStar_ST.op_Bang stack  in
    match uu____10063 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10117 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____10189  ->
           let uu____10190 = snapshot_stack env  in
           match uu____10190 with
           | (stack_depth,env1) ->
               let uu____10215 = snapshot_query_indices ()  in
               (match uu____10215 with
                | (query_indices_depth,()) ->
                    let uu____10239 = (env1.solver).snapshot msg  in
                    (match uu____10239 with
                     | (solver_depth,()) ->
                         let uu____10281 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____10281 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___239_10327 = env1  in
                                 {
                                   solver = (uu___239_10327.solver);
                                   range = (uu___239_10327.range);
                                   curmodule = (uu___239_10327.curmodule);
                                   gamma = (uu___239_10327.gamma);
                                   gamma_sig = (uu___239_10327.gamma_sig);
                                   gamma_cache = (uu___239_10327.gamma_cache);
                                   modules = (uu___239_10327.modules);
                                   expected_typ =
                                     (uu___239_10327.expected_typ);
                                   sigtab = (uu___239_10327.sigtab);
                                   attrtab = (uu___239_10327.attrtab);
                                   is_pattern = (uu___239_10327.is_pattern);
                                   instantiate_imp =
                                     (uu___239_10327.instantiate_imp);
                                   effects = (uu___239_10327.effects);
                                   generalize = (uu___239_10327.generalize);
                                   letrecs = (uu___239_10327.letrecs);
                                   top_level = (uu___239_10327.top_level);
                                   check_uvars = (uu___239_10327.check_uvars);
                                   use_eq = (uu___239_10327.use_eq);
                                   is_iface = (uu___239_10327.is_iface);
                                   admit = (uu___239_10327.admit);
                                   lax = (uu___239_10327.lax);
                                   lax_universes =
                                     (uu___239_10327.lax_universes);
                                   phase1 = (uu___239_10327.phase1);
                                   failhard = (uu___239_10327.failhard);
                                   nosynth = (uu___239_10327.nosynth);
                                   uvar_subtyping =
                                     (uu___239_10327.uvar_subtyping);
                                   tc_term = (uu___239_10327.tc_term);
                                   type_of = (uu___239_10327.type_of);
                                   universe_of = (uu___239_10327.universe_of);
                                   check_type_of =
                                     (uu___239_10327.check_type_of);
                                   use_bv_sorts =
                                     (uu___239_10327.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___239_10327.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___239_10327.normalized_eff_names);
                                   proof_ns = (uu___239_10327.proof_ns);
                                   synth_hook = (uu___239_10327.synth_hook);
                                   splice = (uu___239_10327.splice);
                                   is_native_tactic =
                                     (uu___239_10327.is_native_tactic);
                                   identifier_info =
                                     (uu___239_10327.identifier_info);
                                   tc_hooks = (uu___239_10327.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___239_10327.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____10358  ->
             let uu____10359 =
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
             match uu____10359 with
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
                             ((let uu____10485 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____10485
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____10496 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____10496
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____10523,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____10555 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10581  ->
                  match uu____10581 with
                  | (m,uu____10587) -> FStar_Ident.lid_equals l m))
           in
        (match uu____10555 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_10595 = env  in
               {
                 solver = (uu___240_10595.solver);
                 range = (uu___240_10595.range);
                 curmodule = (uu___240_10595.curmodule);
                 gamma = (uu___240_10595.gamma);
                 gamma_sig = (uu___240_10595.gamma_sig);
                 gamma_cache = (uu___240_10595.gamma_cache);
                 modules = (uu___240_10595.modules);
                 expected_typ = (uu___240_10595.expected_typ);
                 sigtab = (uu___240_10595.sigtab);
                 attrtab = (uu___240_10595.attrtab);
                 is_pattern = (uu___240_10595.is_pattern);
                 instantiate_imp = (uu___240_10595.instantiate_imp);
                 effects = (uu___240_10595.effects);
                 generalize = (uu___240_10595.generalize);
                 letrecs = (uu___240_10595.letrecs);
                 top_level = (uu___240_10595.top_level);
                 check_uvars = (uu___240_10595.check_uvars);
                 use_eq = (uu___240_10595.use_eq);
                 is_iface = (uu___240_10595.is_iface);
                 admit = (uu___240_10595.admit);
                 lax = (uu___240_10595.lax);
                 lax_universes = (uu___240_10595.lax_universes);
                 phase1 = (uu___240_10595.phase1);
                 failhard = (uu___240_10595.failhard);
                 nosynth = (uu___240_10595.nosynth);
                 uvar_subtyping = (uu___240_10595.uvar_subtyping);
                 tc_term = (uu___240_10595.tc_term);
                 type_of = (uu___240_10595.type_of);
                 universe_of = (uu___240_10595.universe_of);
                 check_type_of = (uu___240_10595.check_type_of);
                 use_bv_sorts = (uu___240_10595.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_10595.normalized_eff_names);
                 proof_ns = (uu___240_10595.proof_ns);
                 synth_hook = (uu___240_10595.synth_hook);
                 splice = (uu___240_10595.splice);
                 is_native_tactic = (uu___240_10595.is_native_tactic);
                 identifier_info = (uu___240_10595.identifier_info);
                 tc_hooks = (uu___240_10595.tc_hooks);
                 dsenv = (uu___240_10595.dsenv);
                 dep_graph = (uu___240_10595.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____10608,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___241_10617 = env  in
               {
                 solver = (uu___241_10617.solver);
                 range = (uu___241_10617.range);
                 curmodule = (uu___241_10617.curmodule);
                 gamma = (uu___241_10617.gamma);
                 gamma_sig = (uu___241_10617.gamma_sig);
                 gamma_cache = (uu___241_10617.gamma_cache);
                 modules = (uu___241_10617.modules);
                 expected_typ = (uu___241_10617.expected_typ);
                 sigtab = (uu___241_10617.sigtab);
                 attrtab = (uu___241_10617.attrtab);
                 is_pattern = (uu___241_10617.is_pattern);
                 instantiate_imp = (uu___241_10617.instantiate_imp);
                 effects = (uu___241_10617.effects);
                 generalize = (uu___241_10617.generalize);
                 letrecs = (uu___241_10617.letrecs);
                 top_level = (uu___241_10617.top_level);
                 check_uvars = (uu___241_10617.check_uvars);
                 use_eq = (uu___241_10617.use_eq);
                 is_iface = (uu___241_10617.is_iface);
                 admit = (uu___241_10617.admit);
                 lax = (uu___241_10617.lax);
                 lax_universes = (uu___241_10617.lax_universes);
                 phase1 = (uu___241_10617.phase1);
                 failhard = (uu___241_10617.failhard);
                 nosynth = (uu___241_10617.nosynth);
                 uvar_subtyping = (uu___241_10617.uvar_subtyping);
                 tc_term = (uu___241_10617.tc_term);
                 type_of = (uu___241_10617.type_of);
                 universe_of = (uu___241_10617.universe_of);
                 check_type_of = (uu___241_10617.check_type_of);
                 use_bv_sorts = (uu___241_10617.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___241_10617.normalized_eff_names);
                 proof_ns = (uu___241_10617.proof_ns);
                 synth_hook = (uu___241_10617.synth_hook);
                 splice = (uu___241_10617.splice);
                 is_native_tactic = (uu___241_10617.is_native_tactic);
                 identifier_info = (uu___241_10617.identifier_info);
                 tc_hooks = (uu___241_10617.tc_hooks);
                 dsenv = (uu___241_10617.dsenv);
                 dep_graph = (uu___241_10617.dep_graph)
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
        (let uu___242_10651 = e  in
         {
           solver = (uu___242_10651.solver);
           range = r;
           curmodule = (uu___242_10651.curmodule);
           gamma = (uu___242_10651.gamma);
           gamma_sig = (uu___242_10651.gamma_sig);
           gamma_cache = (uu___242_10651.gamma_cache);
           modules = (uu___242_10651.modules);
           expected_typ = (uu___242_10651.expected_typ);
           sigtab = (uu___242_10651.sigtab);
           attrtab = (uu___242_10651.attrtab);
           is_pattern = (uu___242_10651.is_pattern);
           instantiate_imp = (uu___242_10651.instantiate_imp);
           effects = (uu___242_10651.effects);
           generalize = (uu___242_10651.generalize);
           letrecs = (uu___242_10651.letrecs);
           top_level = (uu___242_10651.top_level);
           check_uvars = (uu___242_10651.check_uvars);
           use_eq = (uu___242_10651.use_eq);
           is_iface = (uu___242_10651.is_iface);
           admit = (uu___242_10651.admit);
           lax = (uu___242_10651.lax);
           lax_universes = (uu___242_10651.lax_universes);
           phase1 = (uu___242_10651.phase1);
           failhard = (uu___242_10651.failhard);
           nosynth = (uu___242_10651.nosynth);
           uvar_subtyping = (uu___242_10651.uvar_subtyping);
           tc_term = (uu___242_10651.tc_term);
           type_of = (uu___242_10651.type_of);
           universe_of = (uu___242_10651.universe_of);
           check_type_of = (uu___242_10651.check_type_of);
           use_bv_sorts = (uu___242_10651.use_bv_sorts);
           qtbl_name_and_index = (uu___242_10651.qtbl_name_and_index);
           normalized_eff_names = (uu___242_10651.normalized_eff_names);
           proof_ns = (uu___242_10651.proof_ns);
           synth_hook = (uu___242_10651.synth_hook);
           splice = (uu___242_10651.splice);
           is_native_tactic = (uu___242_10651.is_native_tactic);
           identifier_info = (uu___242_10651.identifier_info);
           tc_hooks = (uu___242_10651.tc_hooks);
           dsenv = (uu___242_10651.dsenv);
           dep_graph = (uu___242_10651.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10667 =
        let uu____10668 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10668 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10667
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10722 =
          let uu____10723 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10723 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10722
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10777 =
          let uu____10778 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10778 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10777
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10832 =
        let uu____10833 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10833 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10832
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___243_10894 = env  in
      {
        solver = (uu___243_10894.solver);
        range = (uu___243_10894.range);
        curmodule = lid;
        gamma = (uu___243_10894.gamma);
        gamma_sig = (uu___243_10894.gamma_sig);
        gamma_cache = (uu___243_10894.gamma_cache);
        modules = (uu___243_10894.modules);
        expected_typ = (uu___243_10894.expected_typ);
        sigtab = (uu___243_10894.sigtab);
        attrtab = (uu___243_10894.attrtab);
        is_pattern = (uu___243_10894.is_pattern);
        instantiate_imp = (uu___243_10894.instantiate_imp);
        effects = (uu___243_10894.effects);
        generalize = (uu___243_10894.generalize);
        letrecs = (uu___243_10894.letrecs);
        top_level = (uu___243_10894.top_level);
        check_uvars = (uu___243_10894.check_uvars);
        use_eq = (uu___243_10894.use_eq);
        is_iface = (uu___243_10894.is_iface);
        admit = (uu___243_10894.admit);
        lax = (uu___243_10894.lax);
        lax_universes = (uu___243_10894.lax_universes);
        phase1 = (uu___243_10894.phase1);
        failhard = (uu___243_10894.failhard);
        nosynth = (uu___243_10894.nosynth);
        uvar_subtyping = (uu___243_10894.uvar_subtyping);
        tc_term = (uu___243_10894.tc_term);
        type_of = (uu___243_10894.type_of);
        universe_of = (uu___243_10894.universe_of);
        check_type_of = (uu___243_10894.check_type_of);
        use_bv_sorts = (uu___243_10894.use_bv_sorts);
        qtbl_name_and_index = (uu___243_10894.qtbl_name_and_index);
        normalized_eff_names = (uu___243_10894.normalized_eff_names);
        proof_ns = (uu___243_10894.proof_ns);
        synth_hook = (uu___243_10894.synth_hook);
        splice = (uu___243_10894.splice);
        is_native_tactic = (uu___243_10894.is_native_tactic);
        identifier_info = (uu___243_10894.identifier_info);
        tc_hooks = (uu___243_10894.tc_hooks);
        dsenv = (uu___243_10894.dsenv);
        dep_graph = (uu___243_10894.dep_graph)
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
      let uu____10921 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10921
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10931 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10931)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10941 =
      let uu____10942 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10942  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10941)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10947  ->
    let uu____10948 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10948
  
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
      | ((formals,t),uu____11004) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____11038 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11038)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___221_11054  ->
    match uu___221_11054 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11080  -> new_u_univ ()))
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
      let uu____11099 = inst_tscheme t  in
      match uu____11099 with
      | (us,t1) ->
          let uu____11110 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11110)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11130  ->
          match uu____11130 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11151 =
                         let uu____11152 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____11153 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____11154 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____11155 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11152 uu____11153 uu____11154 uu____11155
                          in
                       failwith uu____11151)
                    else ();
                    (let uu____11157 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____11157))
               | uu____11166 ->
                   let uu____11167 =
                     let uu____11168 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____11168
                      in
                   failwith uu____11167)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____11174 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11180 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11186 -> false
  
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
             | ([],uu____11228) -> Maybe
             | (uu____11235,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____11254 -> No  in
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
          let uu____11345 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____11345 with
          | FStar_Pervasives_Native.None  ->
              let uu____11368 =
                FStar_Util.find_map env.gamma
                  (fun uu___222_11412  ->
                     match uu___222_11412 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11451 = FStar_Ident.lid_equals lid l  in
                         if uu____11451
                         then
                           let uu____11472 =
                             let uu____11491 =
                               let uu____11506 = inst_tscheme t  in
                               FStar_Util.Inl uu____11506  in
                             let uu____11521 = FStar_Ident.range_of_lid l  in
                             (uu____11491, uu____11521)  in
                           FStar_Pervasives_Native.Some uu____11472
                         else FStar_Pervasives_Native.None
                     | uu____11573 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11368
                (fun uu____11611  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___223_11620  ->
                        match uu___223_11620 with
                        | (uu____11623,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11625);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11626;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11627;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11628;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11629;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11649 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11649
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
                                  uu____11697 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11704 -> cache t  in
                            let uu____11705 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11705 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11711 =
                                   let uu____11712 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11712)
                                    in
                                 maybe_cache uu____11711)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11780 = find_in_sigtab env lid  in
         match uu____11780 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____11860 = lookup_qname env lid  in
      match uu____11860 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____11881,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____11992 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____11992 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____12034 =
          let uu____12037 = lookup_attr env1 attr  in se1 :: uu____12037  in
        FStar_Util.smap_add (attrtab env1) attr uu____12034  in
      FStar_List.iter
        (fun attr  ->
           let uu____12047 =
             let uu____12048 = FStar_Syntax_Subst.compress attr  in
             uu____12048.FStar_Syntax_Syntax.n  in
           match uu____12047 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____12052 =
                 let uu____12053 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____12053.FStar_Ident.str  in
               add_one1 env se uu____12052
           | uu____12054 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12076) ->
          add_sigelts env ses
      | uu____12085 ->
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
            | uu____12100 -> ()))

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
        (fun uu___224_12131  ->
           match uu___224_12131 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12149 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____12210,lb::[]),uu____12212) ->
            let uu____12219 =
              let uu____12228 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____12237 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____12228, uu____12237)  in
            FStar_Pervasives_Native.Some uu____12219
        | FStar_Syntax_Syntax.Sig_let ((uu____12250,lbs),uu____12252) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____12282 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____12294 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____12294
                     then
                       let uu____12305 =
                         let uu____12314 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____12323 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____12314, uu____12323)  in
                       FStar_Pervasives_Native.Some uu____12305
                     else FStar_Pervasives_Native.None)
        | uu____12345 -> FStar_Pervasives_Native.None
  
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
          let uu____12404 =
            let uu____12413 =
              let uu____12418 =
                let uu____12419 =
                  let uu____12422 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____12422
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____12419)  in
              inst_tscheme1 uu____12418  in
            (uu____12413, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12404
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____12444,uu____12445) ->
          let uu____12450 =
            let uu____12459 =
              let uu____12464 =
                let uu____12465 =
                  let uu____12468 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____12468  in
                (us, uu____12465)  in
              inst_tscheme1 uu____12464  in
            (uu____12459, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12450
      | uu____12487 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12575 =
          match uu____12575 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12671,uvs,t,uu____12674,uu____12675,uu____12676);
                      FStar_Syntax_Syntax.sigrng = uu____12677;
                      FStar_Syntax_Syntax.sigquals = uu____12678;
                      FStar_Syntax_Syntax.sigmeta = uu____12679;
                      FStar_Syntax_Syntax.sigattrs = uu____12680;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12701 =
                     let uu____12710 = inst_tscheme1 (uvs, t)  in
                     (uu____12710, rng)  in
                   FStar_Pervasives_Native.Some uu____12701
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12734;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12736;
                      FStar_Syntax_Syntax.sigattrs = uu____12737;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12754 =
                     let uu____12755 = in_cur_mod env l  in uu____12755 = Yes
                      in
                   if uu____12754
                   then
                     let uu____12766 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12766
                      then
                        let uu____12779 =
                          let uu____12788 = inst_tscheme1 (uvs, t)  in
                          (uu____12788, rng)  in
                        FStar_Pervasives_Native.Some uu____12779
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12819 =
                        let uu____12828 = inst_tscheme1 (uvs, t)  in
                        (uu____12828, rng)  in
                      FStar_Pervasives_Native.Some uu____12819)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12853,uu____12854);
                      FStar_Syntax_Syntax.sigrng = uu____12855;
                      FStar_Syntax_Syntax.sigquals = uu____12856;
                      FStar_Syntax_Syntax.sigmeta = uu____12857;
                      FStar_Syntax_Syntax.sigattrs = uu____12858;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12899 =
                          let uu____12908 = inst_tscheme1 (uvs, k)  in
                          (uu____12908, rng)  in
                        FStar_Pervasives_Native.Some uu____12899
                    | uu____12929 ->
                        let uu____12930 =
                          let uu____12939 =
                            let uu____12944 =
                              let uu____12945 =
                                let uu____12948 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12948
                                 in
                              (uvs, uu____12945)  in
                            inst_tscheme1 uu____12944  in
                          (uu____12939, rng)  in
                        FStar_Pervasives_Native.Some uu____12930)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12971,uu____12972);
                      FStar_Syntax_Syntax.sigrng = uu____12973;
                      FStar_Syntax_Syntax.sigquals = uu____12974;
                      FStar_Syntax_Syntax.sigmeta = uu____12975;
                      FStar_Syntax_Syntax.sigattrs = uu____12976;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13018 =
                          let uu____13027 = inst_tscheme_with (uvs, k) us  in
                          (uu____13027, rng)  in
                        FStar_Pervasives_Native.Some uu____13018
                    | uu____13048 ->
                        let uu____13049 =
                          let uu____13058 =
                            let uu____13063 =
                              let uu____13064 =
                                let uu____13067 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13067
                                 in
                              (uvs, uu____13064)  in
                            inst_tscheme_with uu____13063 us  in
                          (uu____13058, rng)  in
                        FStar_Pervasives_Native.Some uu____13049)
               | FStar_Util.Inr se ->
                   let uu____13103 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13124;
                          FStar_Syntax_Syntax.sigrng = uu____13125;
                          FStar_Syntax_Syntax.sigquals = uu____13126;
                          FStar_Syntax_Syntax.sigmeta = uu____13127;
                          FStar_Syntax_Syntax.sigattrs = uu____13128;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13143 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____13103
                     (FStar_Util.map_option
                        (fun uu____13191  ->
                           match uu____13191 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____13222 =
          let uu____13233 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____13233 mapper  in
        match uu____13222 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____13307 =
              let uu____13318 =
                let uu____13325 =
                  let uu___244_13328 = t  in
                  let uu____13329 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___244_13328.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____13329;
                    FStar_Syntax_Syntax.vars =
                      (uu___244_13328.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____13325)  in
              (uu____13318, r)  in
            FStar_Pervasives_Native.Some uu____13307
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13376 = lookup_qname env l  in
      match uu____13376 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____13395 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____13447 = try_lookup_bv env bv  in
      match uu____13447 with
      | FStar_Pervasives_Native.None  ->
          let uu____13462 = variable_not_found bv  in
          FStar_Errors.raise_error uu____13462 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____13477 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____13478 =
            let uu____13479 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____13479  in
          (uu____13477, uu____13478)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____13500 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____13500 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____13566 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____13566  in
          let uu____13567 =
            let uu____13576 =
              let uu____13581 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13581)  in
            (uu____13576, r1)  in
          FStar_Pervasives_Native.Some uu____13567
  
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
        let uu____13615 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13615 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13648,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13673 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13673  in
            let uu____13674 =
              let uu____13679 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13679, r1)  in
            FStar_Pervasives_Native.Some uu____13674
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13702 = try_lookup_lid env l  in
      match uu____13702 with
      | FStar_Pervasives_Native.None  ->
          let uu____13729 = name_not_found l  in
          let uu____13734 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13729 uu____13734
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___225_13774  ->
              match uu___225_13774 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13776 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13795 = lookup_qname env lid  in
      match uu____13795 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13804,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13807;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13809;
              FStar_Syntax_Syntax.sigattrs = uu____13810;_},FStar_Pervasives_Native.None
            ),uu____13811)
          ->
          let uu____13860 =
            let uu____13867 =
              let uu____13868 =
                let uu____13871 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13871 t  in
              (uvs, uu____13868)  in
            (uu____13867, q)  in
          FStar_Pervasives_Native.Some uu____13860
      | uu____13884 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13905 = lookup_qname env lid  in
      match uu____13905 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13910,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13913;
              FStar_Syntax_Syntax.sigquals = uu____13914;
              FStar_Syntax_Syntax.sigmeta = uu____13915;
              FStar_Syntax_Syntax.sigattrs = uu____13916;_},FStar_Pervasives_Native.None
            ),uu____13917)
          ->
          let uu____13966 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13966 (uvs, t)
      | uu____13971 ->
          let uu____13972 = name_not_found lid  in
          let uu____13977 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13972 uu____13977
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13996 = lookup_qname env lid  in
      match uu____13996 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14001,uvs,t,uu____14004,uu____14005,uu____14006);
              FStar_Syntax_Syntax.sigrng = uu____14007;
              FStar_Syntax_Syntax.sigquals = uu____14008;
              FStar_Syntax_Syntax.sigmeta = uu____14009;
              FStar_Syntax_Syntax.sigattrs = uu____14010;_},FStar_Pervasives_Native.None
            ),uu____14011)
          ->
          let uu____14064 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14064 (uvs, t)
      | uu____14069 ->
          let uu____14070 = name_not_found lid  in
          let uu____14075 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14070 uu____14075
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14096 = lookup_qname env lid  in
      match uu____14096 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14103,uu____14104,uu____14105,uu____14106,uu____14107,dcs);
              FStar_Syntax_Syntax.sigrng = uu____14109;
              FStar_Syntax_Syntax.sigquals = uu____14110;
              FStar_Syntax_Syntax.sigmeta = uu____14111;
              FStar_Syntax_Syntax.sigattrs = uu____14112;_},uu____14113),uu____14114)
          -> (true, dcs)
      | uu____14175 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____14188 = lookup_qname env lid  in
      match uu____14188 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14189,uu____14190,uu____14191,l,uu____14193,uu____14194);
              FStar_Syntax_Syntax.sigrng = uu____14195;
              FStar_Syntax_Syntax.sigquals = uu____14196;
              FStar_Syntax_Syntax.sigmeta = uu____14197;
              FStar_Syntax_Syntax.sigattrs = uu____14198;_},uu____14199),uu____14200)
          -> l
      | uu____14255 ->
          let uu____14256 =
            let uu____14257 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____14257  in
          failwith uu____14256
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14306)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____14357,lbs),uu____14359)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____14381 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____14381
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____14413 -> FStar_Pervasives_Native.None)
        | uu____14418 -> FStar_Pervasives_Native.None
  
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
        let uu____14448 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____14448
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14473),uu____14474) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____14523 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14544),uu____14545) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____14594 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14615 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____14615
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____14634 = lookup_qname env ftv  in
      match uu____14634 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14638) ->
          let uu____14683 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14683 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14704,t),r) ->
               let uu____14719 =
                 let uu____14720 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14720 t  in
               FStar_Pervasives_Native.Some uu____14719)
      | uu____14721 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14732 = try_lookup_effect_lid env ftv  in
      match uu____14732 with
      | FStar_Pervasives_Native.None  ->
          let uu____14735 = name_not_found ftv  in
          let uu____14740 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14735 uu____14740
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
        let uu____14763 = lookup_qname env lid0  in
        match uu____14763 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14774);
                FStar_Syntax_Syntax.sigrng = uu____14775;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14777;
                FStar_Syntax_Syntax.sigattrs = uu____14778;_},FStar_Pervasives_Native.None
              ),uu____14779)
            ->
            let lid1 =
              let uu____14833 =
                let uu____14834 = FStar_Ident.range_of_lid lid  in
                let uu____14835 =
                  let uu____14836 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14836  in
                FStar_Range.set_use_range uu____14834 uu____14835  in
              FStar_Ident.set_lid_range lid uu____14833  in
            let uu____14837 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___226_14841  ->
                      match uu___226_14841 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14842 -> false))
               in
            if uu____14837
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14856 =
                      let uu____14857 =
                        let uu____14858 = get_range env  in
                        FStar_Range.string_of_range uu____14858  in
                      let uu____14859 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14860 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14857 uu____14859 uu____14860
                       in
                    failwith uu____14856)
                  in
               match (binders, univs1) with
               | ([],uu____14877) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14902,uu____14903::uu____14904::uu____14905) ->
                   let uu____14926 =
                     let uu____14927 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14928 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14927 uu____14928
                      in
                   failwith uu____14926
               | uu____14935 ->
                   let uu____14950 =
                     let uu____14955 =
                       let uu____14956 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14956)  in
                     inst_tscheme_with uu____14955 insts  in
                   (match uu____14950 with
                    | (uu____14969,t) ->
                        let t1 =
                          let uu____14972 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14972 t  in
                        let uu____14973 =
                          let uu____14974 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14974.FStar_Syntax_Syntax.n  in
                        (match uu____14973 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____15009 -> failwith "Impossible")))
        | uu____15016 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____15039 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____15039 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____15052,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____15059 = find1 l2  in
            (match uu____15059 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____15066 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____15066 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____15070 = find1 l  in
            (match uu____15070 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____15075 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____15075
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____15089 = lookup_qname env l1  in
      match uu____15089 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____15092;
              FStar_Syntax_Syntax.sigrng = uu____15093;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15095;
              FStar_Syntax_Syntax.sigattrs = uu____15096;_},uu____15097),uu____15098)
          -> q
      | uu____15149 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____15170 =
          let uu____15171 =
            let uu____15172 = FStar_Util.string_of_int i  in
            let uu____15173 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____15172 uu____15173
             in
          failwith uu____15171  in
        let uu____15174 = lookup_datacon env lid  in
        match uu____15174 with
        | (uu____15179,t) ->
            let uu____15181 =
              let uu____15182 = FStar_Syntax_Subst.compress t  in
              uu____15182.FStar_Syntax_Syntax.n  in
            (match uu____15181 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15186) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____15227 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____15227
                      FStar_Pervasives_Native.fst)
             | uu____15238 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15249 = lookup_qname env l  in
      match uu____15249 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15250,uu____15251,uu____15252);
              FStar_Syntax_Syntax.sigrng = uu____15253;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15255;
              FStar_Syntax_Syntax.sigattrs = uu____15256;_},uu____15257),uu____15258)
          ->
          FStar_Util.for_some
            (fun uu___227_15311  ->
               match uu___227_15311 with
               | FStar_Syntax_Syntax.Projector uu____15312 -> true
               | uu____15317 -> false) quals
      | uu____15318 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15329 = lookup_qname env lid  in
      match uu____15329 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15330,uu____15331,uu____15332,uu____15333,uu____15334,uu____15335);
              FStar_Syntax_Syntax.sigrng = uu____15336;
              FStar_Syntax_Syntax.sigquals = uu____15337;
              FStar_Syntax_Syntax.sigmeta = uu____15338;
              FStar_Syntax_Syntax.sigattrs = uu____15339;_},uu____15340),uu____15341)
          -> true
      | uu____15396 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15407 = lookup_qname env lid  in
      match uu____15407 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15408,uu____15409,uu____15410,uu____15411,uu____15412,uu____15413);
              FStar_Syntax_Syntax.sigrng = uu____15414;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15416;
              FStar_Syntax_Syntax.sigattrs = uu____15417;_},uu____15418),uu____15419)
          ->
          FStar_Util.for_some
            (fun uu___228_15480  ->
               match uu___228_15480 with
               | FStar_Syntax_Syntax.RecordType uu____15481 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____15490 -> true
               | uu____15499 -> false) quals
      | uu____15500 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____15506,uu____15507);
            FStar_Syntax_Syntax.sigrng = uu____15508;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____15510;
            FStar_Syntax_Syntax.sigattrs = uu____15511;_},uu____15512),uu____15513)
        ->
        FStar_Util.for_some
          (fun uu___229_15570  ->
             match uu___229_15570 with
             | FStar_Syntax_Syntax.Action uu____15571 -> true
             | uu____15572 -> false) quals
    | uu____15573 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15584 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____15584
  
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
      let uu____15598 =
        let uu____15599 = FStar_Syntax_Util.un_uinst head1  in
        uu____15599.FStar_Syntax_Syntax.n  in
      match uu____15598 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____15603 ->
               true
           | uu____15604 -> false)
      | uu____15605 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15616 = lookup_qname env l  in
      match uu____15616 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____15618),uu____15619) ->
          FStar_Util.for_some
            (fun uu___230_15667  ->
               match uu___230_15667 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____15668 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____15669 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15740 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15756) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15773 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15780 ->
                 FStar_Pervasives_Native.Some true
             | uu____15797 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15798 =
        let uu____15801 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15801 mapper  in
      match uu____15798 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15851 = lookup_qname env lid  in
      match uu____15851 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15852,uu____15853,tps,uu____15855,uu____15856,uu____15857);
              FStar_Syntax_Syntax.sigrng = uu____15858;
              FStar_Syntax_Syntax.sigquals = uu____15859;
              FStar_Syntax_Syntax.sigmeta = uu____15860;
              FStar_Syntax_Syntax.sigattrs = uu____15861;_},uu____15862),uu____15863)
          -> FStar_List.length tps
      | uu____15928 ->
          let uu____15929 = name_not_found lid  in
          let uu____15934 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15929 uu____15934
  
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
           (fun uu____15978  ->
              match uu____15978 with
              | (d,uu____15986) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____16001 = effect_decl_opt env l  in
      match uu____16001 with
      | FStar_Pervasives_Native.None  ->
          let uu____16016 = name_not_found l  in
          let uu____16021 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____16016 uu____16021
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____16043  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____16062  ->
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
        let uu____16093 = FStar_Ident.lid_equals l1 l2  in
        if uu____16093
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____16101 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____16101
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____16109 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____16162  ->
                        match uu____16162 with
                        | (m1,m2,uu____16175,uu____16176,uu____16177) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____16109 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16194 =
                    let uu____16199 =
                      let uu____16200 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____16201 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____16200
                        uu____16201
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____16199)
                     in
                  FStar_Errors.raise_error uu____16194 env.range
              | FStar_Pervasives_Native.Some
                  (uu____16208,uu____16209,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____16242 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____16242
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
  'Auu____16258 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____16258)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____16287 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____16313  ->
                match uu____16313 with
                | (d,uu____16319) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____16287 with
      | FStar_Pervasives_Native.None  ->
          let uu____16330 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____16330
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____16343 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____16343 with
           | (uu____16358,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____16376)::(wp,uu____16378)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____16434 -> failwith "Impossible"))
  
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
          let uu____16489 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____16489
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____16491 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____16491
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
                  let uu____16499 = get_range env  in
                  let uu____16500 =
                    let uu____16507 =
                      let uu____16508 =
                        let uu____16525 =
                          let uu____16536 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____16536]  in
                        (null_wp, uu____16525)  in
                      FStar_Syntax_Syntax.Tm_app uu____16508  in
                    FStar_Syntax_Syntax.mk uu____16507  in
                  uu____16500 FStar_Pervasives_Native.None uu____16499  in
                let uu____16576 =
                  let uu____16577 =
                    let uu____16588 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____16588]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____16577;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____16576))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___245_16625 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___245_16625.order);
              joins = (uu___245_16625.joins)
            }  in
          let uu___246_16634 = env  in
          {
            solver = (uu___246_16634.solver);
            range = (uu___246_16634.range);
            curmodule = (uu___246_16634.curmodule);
            gamma = (uu___246_16634.gamma);
            gamma_sig = (uu___246_16634.gamma_sig);
            gamma_cache = (uu___246_16634.gamma_cache);
            modules = (uu___246_16634.modules);
            expected_typ = (uu___246_16634.expected_typ);
            sigtab = (uu___246_16634.sigtab);
            attrtab = (uu___246_16634.attrtab);
            is_pattern = (uu___246_16634.is_pattern);
            instantiate_imp = (uu___246_16634.instantiate_imp);
            effects;
            generalize = (uu___246_16634.generalize);
            letrecs = (uu___246_16634.letrecs);
            top_level = (uu___246_16634.top_level);
            check_uvars = (uu___246_16634.check_uvars);
            use_eq = (uu___246_16634.use_eq);
            is_iface = (uu___246_16634.is_iface);
            admit = (uu___246_16634.admit);
            lax = (uu___246_16634.lax);
            lax_universes = (uu___246_16634.lax_universes);
            phase1 = (uu___246_16634.phase1);
            failhard = (uu___246_16634.failhard);
            nosynth = (uu___246_16634.nosynth);
            uvar_subtyping = (uu___246_16634.uvar_subtyping);
            tc_term = (uu___246_16634.tc_term);
            type_of = (uu___246_16634.type_of);
            universe_of = (uu___246_16634.universe_of);
            check_type_of = (uu___246_16634.check_type_of);
            use_bv_sorts = (uu___246_16634.use_bv_sorts);
            qtbl_name_and_index = (uu___246_16634.qtbl_name_and_index);
            normalized_eff_names = (uu___246_16634.normalized_eff_names);
            proof_ns = (uu___246_16634.proof_ns);
            synth_hook = (uu___246_16634.synth_hook);
            splice = (uu___246_16634.splice);
            is_native_tactic = (uu___246_16634.is_native_tactic);
            identifier_info = (uu___246_16634.identifier_info);
            tc_hooks = (uu___246_16634.tc_hooks);
            dsenv = (uu___246_16634.dsenv);
            dep_graph = (uu___246_16634.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____16664 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____16664  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16822 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16823 = l1 u t wp e  in
                                l2 u t uu____16822 uu____16823))
                | uu____16824 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16896 = inst_tscheme_with lift_t [u]  in
            match uu____16896 with
            | (uu____16903,lift_t1) ->
                let uu____16905 =
                  let uu____16912 =
                    let uu____16913 =
                      let uu____16930 =
                        let uu____16941 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16950 =
                          let uu____16961 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16961]  in
                        uu____16941 :: uu____16950  in
                      (lift_t1, uu____16930)  in
                    FStar_Syntax_Syntax.Tm_app uu____16913  in
                  FStar_Syntax_Syntax.mk uu____16912  in
                uu____16905 FStar_Pervasives_Native.None
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
            let uu____17073 = inst_tscheme_with lift_t [u]  in
            match uu____17073 with
            | (uu____17080,lift_t1) ->
                let uu____17082 =
                  let uu____17089 =
                    let uu____17090 =
                      let uu____17107 =
                        let uu____17118 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17127 =
                          let uu____17138 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____17147 =
                            let uu____17158 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____17158]  in
                          uu____17138 :: uu____17147  in
                        uu____17118 :: uu____17127  in
                      (lift_t1, uu____17107)  in
                    FStar_Syntax_Syntax.Tm_app uu____17090  in
                  FStar_Syntax_Syntax.mk uu____17089  in
                uu____17082 FStar_Pervasives_Native.None
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
              let uu____17260 =
                let uu____17261 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____17261
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____17260  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____17265 =
              let uu____17266 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____17266  in
            let uu____17267 =
              let uu____17268 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____17294 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____17294)
                 in
              FStar_Util.dflt "none" uu____17268  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____17265
              uu____17267
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____17320  ->
                    match uu____17320 with
                    | (e,uu____17328) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____17351 =
            match uu____17351 with
            | (i,j) ->
                let uu____17362 = FStar_Ident.lid_equals i j  in
                if uu____17362
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
              let uu____17394 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____17404 = FStar_Ident.lid_equals i k  in
                        if uu____17404
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____17415 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____17415
                                  then []
                                  else
                                    (let uu____17419 =
                                       let uu____17428 =
                                         find_edge order1 (i, k)  in
                                       let uu____17431 =
                                         find_edge order1 (k, j)  in
                                       (uu____17428, uu____17431)  in
                                     match uu____17419 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____17446 =
                                           compose_edges e1 e2  in
                                         [uu____17446]
                                     | uu____17447 -> [])))))
                 in
              FStar_List.append order1 uu____17394  in
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
                   let uu____17477 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____17479 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____17479
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____17477
                   then
                     let uu____17484 =
                       let uu____17489 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____17489)
                        in
                     let uu____17490 = get_range env  in
                     FStar_Errors.raise_error uu____17484 uu____17490
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____17567 = FStar_Ident.lid_equals i j
                                   in
                                if uu____17567
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____17616 =
                                              let uu____17625 =
                                                find_edge order2 (i, k)  in
                                              let uu____17628 =
                                                find_edge order2 (j, k)  in
                                              (uu____17625, uu____17628)  in
                                            match uu____17616 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____17670,uu____17671)
                                                     ->
                                                     let uu____17678 =
                                                       let uu____17683 =
                                                         let uu____17684 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17684
                                                          in
                                                       let uu____17687 =
                                                         let uu____17688 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17688
                                                          in
                                                       (uu____17683,
                                                         uu____17687)
                                                        in
                                                     (match uu____17678 with
                                                      | (true ,true ) ->
                                                          let uu____17699 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____17699
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
                                            | uu____17724 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___247_17797 = env.effects  in
              { decls = (uu___247_17797.decls); order = order2; joins }  in
            let uu___248_17798 = env  in
            {
              solver = (uu___248_17798.solver);
              range = (uu___248_17798.range);
              curmodule = (uu___248_17798.curmodule);
              gamma = (uu___248_17798.gamma);
              gamma_sig = (uu___248_17798.gamma_sig);
              gamma_cache = (uu___248_17798.gamma_cache);
              modules = (uu___248_17798.modules);
              expected_typ = (uu___248_17798.expected_typ);
              sigtab = (uu___248_17798.sigtab);
              attrtab = (uu___248_17798.attrtab);
              is_pattern = (uu___248_17798.is_pattern);
              instantiate_imp = (uu___248_17798.instantiate_imp);
              effects;
              generalize = (uu___248_17798.generalize);
              letrecs = (uu___248_17798.letrecs);
              top_level = (uu___248_17798.top_level);
              check_uvars = (uu___248_17798.check_uvars);
              use_eq = (uu___248_17798.use_eq);
              is_iface = (uu___248_17798.is_iface);
              admit = (uu___248_17798.admit);
              lax = (uu___248_17798.lax);
              lax_universes = (uu___248_17798.lax_universes);
              phase1 = (uu___248_17798.phase1);
              failhard = (uu___248_17798.failhard);
              nosynth = (uu___248_17798.nosynth);
              uvar_subtyping = (uu___248_17798.uvar_subtyping);
              tc_term = (uu___248_17798.tc_term);
              type_of = (uu___248_17798.type_of);
              universe_of = (uu___248_17798.universe_of);
              check_type_of = (uu___248_17798.check_type_of);
              use_bv_sorts = (uu___248_17798.use_bv_sorts);
              qtbl_name_and_index = (uu___248_17798.qtbl_name_and_index);
              normalized_eff_names = (uu___248_17798.normalized_eff_names);
              proof_ns = (uu___248_17798.proof_ns);
              synth_hook = (uu___248_17798.synth_hook);
              splice = (uu___248_17798.splice);
              is_native_tactic = (uu___248_17798.is_native_tactic);
              identifier_info = (uu___248_17798.identifier_info);
              tc_hooks = (uu___248_17798.tc_hooks);
              dsenv = (uu___248_17798.dsenv);
              dep_graph = (uu___248_17798.dep_graph)
            }))
      | uu____17799 -> env
  
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
        | uu____17827 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17839 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17839 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17856 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17856 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17878 =
                     let uu____17883 =
                       let uu____17884 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17891 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17900 =
                         let uu____17901 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17901  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17884 uu____17891 uu____17900
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17883)
                      in
                   FStar_Errors.raise_error uu____17878
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17906 =
                     let uu____17917 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17917 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17954  ->
                        fun uu____17955  ->
                          match (uu____17954, uu____17955) with
                          | ((x,uu____17985),(t,uu____17987)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17906
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____18018 =
                     let uu___249_18019 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___249_18019.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___249_18019.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___249_18019.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___249_18019.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____18018
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
          let uu____18049 = effect_decl_opt env effect_name  in
          match uu____18049 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____18082 =
                only_reifiable &&
                  (let uu____18084 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____18084)
                 in
              if uu____18082
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____18100 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____18123 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____18160 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____18160
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____18161 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____18161
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____18175 =
                       let uu____18178 = get_range env  in
                       let uu____18179 =
                         let uu____18186 =
                           let uu____18187 =
                             let uu____18204 =
                               let uu____18215 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____18215; wp]  in
                             (repr, uu____18204)  in
                           FStar_Syntax_Syntax.Tm_app uu____18187  in
                         FStar_Syntax_Syntax.mk uu____18186  in
                       uu____18179 FStar_Pervasives_Native.None uu____18178
                        in
                     FStar_Pervasives_Native.Some uu____18175)
  
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
          let uu____18305 =
            let uu____18310 =
              let uu____18311 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____18311
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____18310)  in
          let uu____18312 = get_range env  in
          FStar_Errors.raise_error uu____18305 uu____18312  in
        let uu____18313 = effect_repr_aux true env c u_c  in
        match uu____18313 with
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
      | uu____18359 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____18370 =
        let uu____18371 = FStar_Syntax_Subst.compress t  in
        uu____18371.FStar_Syntax_Syntax.n  in
      match uu____18370 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____18374,c) ->
          is_reifiable_comp env c
      | uu____18396 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___250_18417 = env  in
        {
          solver = (uu___250_18417.solver);
          range = (uu___250_18417.range);
          curmodule = (uu___250_18417.curmodule);
          gamma = (uu___250_18417.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___250_18417.gamma_cache);
          modules = (uu___250_18417.modules);
          expected_typ = (uu___250_18417.expected_typ);
          sigtab = (uu___250_18417.sigtab);
          attrtab = (uu___250_18417.attrtab);
          is_pattern = (uu___250_18417.is_pattern);
          instantiate_imp = (uu___250_18417.instantiate_imp);
          effects = (uu___250_18417.effects);
          generalize = (uu___250_18417.generalize);
          letrecs = (uu___250_18417.letrecs);
          top_level = (uu___250_18417.top_level);
          check_uvars = (uu___250_18417.check_uvars);
          use_eq = (uu___250_18417.use_eq);
          is_iface = (uu___250_18417.is_iface);
          admit = (uu___250_18417.admit);
          lax = (uu___250_18417.lax);
          lax_universes = (uu___250_18417.lax_universes);
          phase1 = (uu___250_18417.phase1);
          failhard = (uu___250_18417.failhard);
          nosynth = (uu___250_18417.nosynth);
          uvar_subtyping = (uu___250_18417.uvar_subtyping);
          tc_term = (uu___250_18417.tc_term);
          type_of = (uu___250_18417.type_of);
          universe_of = (uu___250_18417.universe_of);
          check_type_of = (uu___250_18417.check_type_of);
          use_bv_sorts = (uu___250_18417.use_bv_sorts);
          qtbl_name_and_index = (uu___250_18417.qtbl_name_and_index);
          normalized_eff_names = (uu___250_18417.normalized_eff_names);
          proof_ns = (uu___250_18417.proof_ns);
          synth_hook = (uu___250_18417.synth_hook);
          splice = (uu___250_18417.splice);
          is_native_tactic = (uu___250_18417.is_native_tactic);
          identifier_info = (uu___250_18417.identifier_info);
          tc_hooks = (uu___250_18417.tc_hooks);
          dsenv = (uu___250_18417.dsenv);
          dep_graph = (uu___250_18417.dep_graph)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___251_18430 = env  in
      {
        solver = (uu___251_18430.solver);
        range = (uu___251_18430.range);
        curmodule = (uu___251_18430.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___251_18430.gamma_sig);
        gamma_cache = (uu___251_18430.gamma_cache);
        modules = (uu___251_18430.modules);
        expected_typ = (uu___251_18430.expected_typ);
        sigtab = (uu___251_18430.sigtab);
        attrtab = (uu___251_18430.attrtab);
        is_pattern = (uu___251_18430.is_pattern);
        instantiate_imp = (uu___251_18430.instantiate_imp);
        effects = (uu___251_18430.effects);
        generalize = (uu___251_18430.generalize);
        letrecs = (uu___251_18430.letrecs);
        top_level = (uu___251_18430.top_level);
        check_uvars = (uu___251_18430.check_uvars);
        use_eq = (uu___251_18430.use_eq);
        is_iface = (uu___251_18430.is_iface);
        admit = (uu___251_18430.admit);
        lax = (uu___251_18430.lax);
        lax_universes = (uu___251_18430.lax_universes);
        phase1 = (uu___251_18430.phase1);
        failhard = (uu___251_18430.failhard);
        nosynth = (uu___251_18430.nosynth);
        uvar_subtyping = (uu___251_18430.uvar_subtyping);
        tc_term = (uu___251_18430.tc_term);
        type_of = (uu___251_18430.type_of);
        universe_of = (uu___251_18430.universe_of);
        check_type_of = (uu___251_18430.check_type_of);
        use_bv_sorts = (uu___251_18430.use_bv_sorts);
        qtbl_name_and_index = (uu___251_18430.qtbl_name_and_index);
        normalized_eff_names = (uu___251_18430.normalized_eff_names);
        proof_ns = (uu___251_18430.proof_ns);
        synth_hook = (uu___251_18430.synth_hook);
        splice = (uu___251_18430.splice);
        is_native_tactic = (uu___251_18430.is_native_tactic);
        identifier_info = (uu___251_18430.identifier_info);
        tc_hooks = (uu___251_18430.tc_hooks);
        dsenv = (uu___251_18430.dsenv);
        dep_graph = (uu___251_18430.dep_graph)
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
            (let uu___252_18485 = env  in
             {
               solver = (uu___252_18485.solver);
               range = (uu___252_18485.range);
               curmodule = (uu___252_18485.curmodule);
               gamma = rest;
               gamma_sig = (uu___252_18485.gamma_sig);
               gamma_cache = (uu___252_18485.gamma_cache);
               modules = (uu___252_18485.modules);
               expected_typ = (uu___252_18485.expected_typ);
               sigtab = (uu___252_18485.sigtab);
               attrtab = (uu___252_18485.attrtab);
               is_pattern = (uu___252_18485.is_pattern);
               instantiate_imp = (uu___252_18485.instantiate_imp);
               effects = (uu___252_18485.effects);
               generalize = (uu___252_18485.generalize);
               letrecs = (uu___252_18485.letrecs);
               top_level = (uu___252_18485.top_level);
               check_uvars = (uu___252_18485.check_uvars);
               use_eq = (uu___252_18485.use_eq);
               is_iface = (uu___252_18485.is_iface);
               admit = (uu___252_18485.admit);
               lax = (uu___252_18485.lax);
               lax_universes = (uu___252_18485.lax_universes);
               phase1 = (uu___252_18485.phase1);
               failhard = (uu___252_18485.failhard);
               nosynth = (uu___252_18485.nosynth);
               uvar_subtyping = (uu___252_18485.uvar_subtyping);
               tc_term = (uu___252_18485.tc_term);
               type_of = (uu___252_18485.type_of);
               universe_of = (uu___252_18485.universe_of);
               check_type_of = (uu___252_18485.check_type_of);
               use_bv_sorts = (uu___252_18485.use_bv_sorts);
               qtbl_name_and_index = (uu___252_18485.qtbl_name_and_index);
               normalized_eff_names = (uu___252_18485.normalized_eff_names);
               proof_ns = (uu___252_18485.proof_ns);
               synth_hook = (uu___252_18485.synth_hook);
               splice = (uu___252_18485.splice);
               is_native_tactic = (uu___252_18485.is_native_tactic);
               identifier_info = (uu___252_18485.identifier_info);
               tc_hooks = (uu___252_18485.tc_hooks);
               dsenv = (uu___252_18485.dsenv);
               dep_graph = (uu___252_18485.dep_graph)
             }))
    | uu____18486 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____18514  ->
             match uu____18514 with | (x,uu____18522) -> push_bv env1 x) env
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
            let uu___253_18556 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___253_18556.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___253_18556.FStar_Syntax_Syntax.index);
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
      (let uu___254_18596 = env  in
       {
         solver = (uu___254_18596.solver);
         range = (uu___254_18596.range);
         curmodule = (uu___254_18596.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___254_18596.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___254_18596.sigtab);
         attrtab = (uu___254_18596.attrtab);
         is_pattern = (uu___254_18596.is_pattern);
         instantiate_imp = (uu___254_18596.instantiate_imp);
         effects = (uu___254_18596.effects);
         generalize = (uu___254_18596.generalize);
         letrecs = (uu___254_18596.letrecs);
         top_level = (uu___254_18596.top_level);
         check_uvars = (uu___254_18596.check_uvars);
         use_eq = (uu___254_18596.use_eq);
         is_iface = (uu___254_18596.is_iface);
         admit = (uu___254_18596.admit);
         lax = (uu___254_18596.lax);
         lax_universes = (uu___254_18596.lax_universes);
         phase1 = (uu___254_18596.phase1);
         failhard = (uu___254_18596.failhard);
         nosynth = (uu___254_18596.nosynth);
         uvar_subtyping = (uu___254_18596.uvar_subtyping);
         tc_term = (uu___254_18596.tc_term);
         type_of = (uu___254_18596.type_of);
         universe_of = (uu___254_18596.universe_of);
         check_type_of = (uu___254_18596.check_type_of);
         use_bv_sorts = (uu___254_18596.use_bv_sorts);
         qtbl_name_and_index = (uu___254_18596.qtbl_name_and_index);
         normalized_eff_names = (uu___254_18596.normalized_eff_names);
         proof_ns = (uu___254_18596.proof_ns);
         synth_hook = (uu___254_18596.synth_hook);
         splice = (uu___254_18596.splice);
         is_native_tactic = (uu___254_18596.is_native_tactic);
         identifier_info = (uu___254_18596.identifier_info);
         tc_hooks = (uu___254_18596.tc_hooks);
         dsenv = (uu___254_18596.dsenv);
         dep_graph = (uu___254_18596.dep_graph)
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
        let uu____18638 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____18638 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____18666 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____18666)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___255_18681 = env  in
      {
        solver = (uu___255_18681.solver);
        range = (uu___255_18681.range);
        curmodule = (uu___255_18681.curmodule);
        gamma = (uu___255_18681.gamma);
        gamma_sig = (uu___255_18681.gamma_sig);
        gamma_cache = (uu___255_18681.gamma_cache);
        modules = (uu___255_18681.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___255_18681.sigtab);
        attrtab = (uu___255_18681.attrtab);
        is_pattern = (uu___255_18681.is_pattern);
        instantiate_imp = (uu___255_18681.instantiate_imp);
        effects = (uu___255_18681.effects);
        generalize = (uu___255_18681.generalize);
        letrecs = (uu___255_18681.letrecs);
        top_level = (uu___255_18681.top_level);
        check_uvars = (uu___255_18681.check_uvars);
        use_eq = false;
        is_iface = (uu___255_18681.is_iface);
        admit = (uu___255_18681.admit);
        lax = (uu___255_18681.lax);
        lax_universes = (uu___255_18681.lax_universes);
        phase1 = (uu___255_18681.phase1);
        failhard = (uu___255_18681.failhard);
        nosynth = (uu___255_18681.nosynth);
        uvar_subtyping = (uu___255_18681.uvar_subtyping);
        tc_term = (uu___255_18681.tc_term);
        type_of = (uu___255_18681.type_of);
        universe_of = (uu___255_18681.universe_of);
        check_type_of = (uu___255_18681.check_type_of);
        use_bv_sorts = (uu___255_18681.use_bv_sorts);
        qtbl_name_and_index = (uu___255_18681.qtbl_name_and_index);
        normalized_eff_names = (uu___255_18681.normalized_eff_names);
        proof_ns = (uu___255_18681.proof_ns);
        synth_hook = (uu___255_18681.synth_hook);
        splice = (uu___255_18681.splice);
        is_native_tactic = (uu___255_18681.is_native_tactic);
        identifier_info = (uu___255_18681.identifier_info);
        tc_hooks = (uu___255_18681.tc_hooks);
        dsenv = (uu___255_18681.dsenv);
        dep_graph = (uu___255_18681.dep_graph)
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
    let uu____18709 = expected_typ env_  in
    ((let uu___256_18715 = env_  in
      {
        solver = (uu___256_18715.solver);
        range = (uu___256_18715.range);
        curmodule = (uu___256_18715.curmodule);
        gamma = (uu___256_18715.gamma);
        gamma_sig = (uu___256_18715.gamma_sig);
        gamma_cache = (uu___256_18715.gamma_cache);
        modules = (uu___256_18715.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___256_18715.sigtab);
        attrtab = (uu___256_18715.attrtab);
        is_pattern = (uu___256_18715.is_pattern);
        instantiate_imp = (uu___256_18715.instantiate_imp);
        effects = (uu___256_18715.effects);
        generalize = (uu___256_18715.generalize);
        letrecs = (uu___256_18715.letrecs);
        top_level = (uu___256_18715.top_level);
        check_uvars = (uu___256_18715.check_uvars);
        use_eq = false;
        is_iface = (uu___256_18715.is_iface);
        admit = (uu___256_18715.admit);
        lax = (uu___256_18715.lax);
        lax_universes = (uu___256_18715.lax_universes);
        phase1 = (uu___256_18715.phase1);
        failhard = (uu___256_18715.failhard);
        nosynth = (uu___256_18715.nosynth);
        uvar_subtyping = (uu___256_18715.uvar_subtyping);
        tc_term = (uu___256_18715.tc_term);
        type_of = (uu___256_18715.type_of);
        universe_of = (uu___256_18715.universe_of);
        check_type_of = (uu___256_18715.check_type_of);
        use_bv_sorts = (uu___256_18715.use_bv_sorts);
        qtbl_name_and_index = (uu___256_18715.qtbl_name_and_index);
        normalized_eff_names = (uu___256_18715.normalized_eff_names);
        proof_ns = (uu___256_18715.proof_ns);
        synth_hook = (uu___256_18715.synth_hook);
        splice = (uu___256_18715.splice);
        is_native_tactic = (uu___256_18715.is_native_tactic);
        identifier_info = (uu___256_18715.identifier_info);
        tc_hooks = (uu___256_18715.tc_hooks);
        dsenv = (uu___256_18715.dsenv);
        dep_graph = (uu___256_18715.dep_graph)
      }), uu____18709)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____18725 =
      let uu____18728 = FStar_Ident.id_of_text ""  in [uu____18728]  in
    FStar_Ident.lid_of_ids uu____18725  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____18734 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____18734
        then
          let uu____18737 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____18737 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___257_18764 = env  in
       {
         solver = (uu___257_18764.solver);
         range = (uu___257_18764.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_18764.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___257_18764.expected_typ);
         sigtab = (uu___257_18764.sigtab);
         attrtab = (uu___257_18764.attrtab);
         is_pattern = (uu___257_18764.is_pattern);
         instantiate_imp = (uu___257_18764.instantiate_imp);
         effects = (uu___257_18764.effects);
         generalize = (uu___257_18764.generalize);
         letrecs = (uu___257_18764.letrecs);
         top_level = (uu___257_18764.top_level);
         check_uvars = (uu___257_18764.check_uvars);
         use_eq = (uu___257_18764.use_eq);
         is_iface = (uu___257_18764.is_iface);
         admit = (uu___257_18764.admit);
         lax = (uu___257_18764.lax);
         lax_universes = (uu___257_18764.lax_universes);
         phase1 = (uu___257_18764.phase1);
         failhard = (uu___257_18764.failhard);
         nosynth = (uu___257_18764.nosynth);
         uvar_subtyping = (uu___257_18764.uvar_subtyping);
         tc_term = (uu___257_18764.tc_term);
         type_of = (uu___257_18764.type_of);
         universe_of = (uu___257_18764.universe_of);
         check_type_of = (uu___257_18764.check_type_of);
         use_bv_sorts = (uu___257_18764.use_bv_sorts);
         qtbl_name_and_index = (uu___257_18764.qtbl_name_and_index);
         normalized_eff_names = (uu___257_18764.normalized_eff_names);
         proof_ns = (uu___257_18764.proof_ns);
         synth_hook = (uu___257_18764.synth_hook);
         splice = (uu___257_18764.splice);
         is_native_tactic = (uu___257_18764.is_native_tactic);
         identifier_info = (uu___257_18764.identifier_info);
         tc_hooks = (uu___257_18764.tc_hooks);
         dsenv = (uu___257_18764.dsenv);
         dep_graph = (uu___257_18764.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18815)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18819,(uu____18820,t)))::tl1
          ->
          let uu____18841 =
            let uu____18844 = FStar_Syntax_Free.uvars t  in
            ext out uu____18844  in
          aux uu____18841 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18847;
            FStar_Syntax_Syntax.index = uu____18848;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18855 =
            let uu____18858 = FStar_Syntax_Free.uvars t  in
            ext out uu____18858  in
          aux uu____18855 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18915)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18919,(uu____18920,t)))::tl1
          ->
          let uu____18941 =
            let uu____18944 = FStar_Syntax_Free.univs t  in
            ext out uu____18944  in
          aux uu____18941 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18947;
            FStar_Syntax_Syntax.index = uu____18948;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18955 =
            let uu____18958 = FStar_Syntax_Free.univs t  in
            ext out uu____18958  in
          aux uu____18955 tl1
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
          let uu____19019 = FStar_Util.set_add uname out  in
          aux uu____19019 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19022,(uu____19023,t)))::tl1
          ->
          let uu____19044 =
            let uu____19047 = FStar_Syntax_Free.univnames t  in
            ext out uu____19047  in
          aux uu____19044 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19050;
            FStar_Syntax_Syntax.index = uu____19051;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19058 =
            let uu____19061 = FStar_Syntax_Free.univnames t  in
            ext out uu____19061  in
          aux uu____19058 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___231_19081  ->
            match uu___231_19081 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____19085 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____19098 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____19108 =
      let uu____19117 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____19117
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____19108 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____19161 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___232_19171  ->
              match uu___232_19171 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____19173 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____19173
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____19176) ->
                  let uu____19193 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____19193))
       in
    FStar_All.pipe_right uu____19161 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___233_19200  ->
    match uu___233_19200 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____19202 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____19202
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____19222  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____19264) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____19283,uu____19284) -> false  in
      let uu____19293 =
        FStar_List.tryFind
          (fun uu____19311  ->
             match uu____19311 with | (p,uu____19319) -> list_prefix p path)
          env.proof_ns
         in
      match uu____19293 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____19330,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19352 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____19352
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___258_19370 = e  in
        {
          solver = (uu___258_19370.solver);
          range = (uu___258_19370.range);
          curmodule = (uu___258_19370.curmodule);
          gamma = (uu___258_19370.gamma);
          gamma_sig = (uu___258_19370.gamma_sig);
          gamma_cache = (uu___258_19370.gamma_cache);
          modules = (uu___258_19370.modules);
          expected_typ = (uu___258_19370.expected_typ);
          sigtab = (uu___258_19370.sigtab);
          attrtab = (uu___258_19370.attrtab);
          is_pattern = (uu___258_19370.is_pattern);
          instantiate_imp = (uu___258_19370.instantiate_imp);
          effects = (uu___258_19370.effects);
          generalize = (uu___258_19370.generalize);
          letrecs = (uu___258_19370.letrecs);
          top_level = (uu___258_19370.top_level);
          check_uvars = (uu___258_19370.check_uvars);
          use_eq = (uu___258_19370.use_eq);
          is_iface = (uu___258_19370.is_iface);
          admit = (uu___258_19370.admit);
          lax = (uu___258_19370.lax);
          lax_universes = (uu___258_19370.lax_universes);
          phase1 = (uu___258_19370.phase1);
          failhard = (uu___258_19370.failhard);
          nosynth = (uu___258_19370.nosynth);
          uvar_subtyping = (uu___258_19370.uvar_subtyping);
          tc_term = (uu___258_19370.tc_term);
          type_of = (uu___258_19370.type_of);
          universe_of = (uu___258_19370.universe_of);
          check_type_of = (uu___258_19370.check_type_of);
          use_bv_sorts = (uu___258_19370.use_bv_sorts);
          qtbl_name_and_index = (uu___258_19370.qtbl_name_and_index);
          normalized_eff_names = (uu___258_19370.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___258_19370.synth_hook);
          splice = (uu___258_19370.splice);
          is_native_tactic = (uu___258_19370.is_native_tactic);
          identifier_info = (uu___258_19370.identifier_info);
          tc_hooks = (uu___258_19370.tc_hooks);
          dsenv = (uu___258_19370.dsenv);
          dep_graph = (uu___258_19370.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___259_19410 = e  in
      {
        solver = (uu___259_19410.solver);
        range = (uu___259_19410.range);
        curmodule = (uu___259_19410.curmodule);
        gamma = (uu___259_19410.gamma);
        gamma_sig = (uu___259_19410.gamma_sig);
        gamma_cache = (uu___259_19410.gamma_cache);
        modules = (uu___259_19410.modules);
        expected_typ = (uu___259_19410.expected_typ);
        sigtab = (uu___259_19410.sigtab);
        attrtab = (uu___259_19410.attrtab);
        is_pattern = (uu___259_19410.is_pattern);
        instantiate_imp = (uu___259_19410.instantiate_imp);
        effects = (uu___259_19410.effects);
        generalize = (uu___259_19410.generalize);
        letrecs = (uu___259_19410.letrecs);
        top_level = (uu___259_19410.top_level);
        check_uvars = (uu___259_19410.check_uvars);
        use_eq = (uu___259_19410.use_eq);
        is_iface = (uu___259_19410.is_iface);
        admit = (uu___259_19410.admit);
        lax = (uu___259_19410.lax);
        lax_universes = (uu___259_19410.lax_universes);
        phase1 = (uu___259_19410.phase1);
        failhard = (uu___259_19410.failhard);
        nosynth = (uu___259_19410.nosynth);
        uvar_subtyping = (uu___259_19410.uvar_subtyping);
        tc_term = (uu___259_19410.tc_term);
        type_of = (uu___259_19410.type_of);
        universe_of = (uu___259_19410.universe_of);
        check_type_of = (uu___259_19410.check_type_of);
        use_bv_sorts = (uu___259_19410.use_bv_sorts);
        qtbl_name_and_index = (uu___259_19410.qtbl_name_and_index);
        normalized_eff_names = (uu___259_19410.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___259_19410.synth_hook);
        splice = (uu___259_19410.splice);
        is_native_tactic = (uu___259_19410.is_native_tactic);
        identifier_info = (uu___259_19410.identifier_info);
        tc_hooks = (uu___259_19410.tc_hooks);
        dsenv = (uu___259_19410.dsenv);
        dep_graph = (uu___259_19410.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____19425 = FStar_Syntax_Free.names t  in
      let uu____19428 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____19425 uu____19428
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____19449 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____19449
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____19457 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____19457
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____19474 =
      match uu____19474 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____19484 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____19484)
       in
    let uu____19486 =
      let uu____19489 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____19489 FStar_List.rev  in
    FStar_All.pipe_right uu____19486 (FStar_String.concat " ")
  
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
                  (let uu____19542 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____19542 with
                   | FStar_Pervasives_Native.Some uu____19545 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____19546 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____19552;
        univ_ineqs = uu____19553; implicits = uu____19554;_} -> true
    | uu____19565 -> false
  
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
          let uu___260_19592 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___260_19592.deferred);
            univ_ineqs = (uu___260_19592.univ_ineqs);
            implicits = (uu___260_19592.implicits)
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
          let uu____19627 = FStar_Options.defensive ()  in
          if uu____19627
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____19631 =
              let uu____19632 =
                let uu____19633 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____19633  in
              Prims.op_Negation uu____19632  in
            (if uu____19631
             then
               let uu____19638 =
                 let uu____19643 =
                   let uu____19644 = FStar_Syntax_Print.term_to_string t  in
                   let uu____19645 =
                     let uu____19646 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____19646
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____19644 uu____19645
                    in
                 (FStar_Errors.Warning_Defensive, uu____19643)  in
               FStar_Errors.log_issue rng uu____19638
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
          let uu____19677 =
            let uu____19678 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19678  in
          if uu____19677
          then ()
          else
            (let uu____19680 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____19680 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____19703 =
            let uu____19704 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19704  in
          if uu____19703
          then ()
          else
            (let uu____19706 = bound_vars e  in
             def_check_closed_in rng msg uu____19706 t)
  
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
          let uu___261_19741 = g  in
          let uu____19742 =
            let uu____19743 =
              let uu____19744 =
                let uu____19751 =
                  let uu____19752 =
                    let uu____19769 =
                      let uu____19780 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____19780]  in
                    (f, uu____19769)  in
                  FStar_Syntax_Syntax.Tm_app uu____19752  in
                FStar_Syntax_Syntax.mk uu____19751  in
              uu____19744 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____19743
             in
          {
            guard_f = uu____19742;
            deferred = (uu___261_19741.deferred);
            univ_ineqs = (uu___261_19741.univ_ineqs);
            implicits = (uu___261_19741.implicits)
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
          let uu___262_19836 = g  in
          let uu____19837 =
            let uu____19838 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19838  in
          {
            guard_f = uu____19837;
            deferred = (uu___262_19836.deferred);
            univ_ineqs = (uu___262_19836.univ_ineqs);
            implicits = (uu___262_19836.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19844 ->
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
          let uu____19859 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19859
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19865 =
      let uu____19866 = FStar_Syntax_Util.unmeta t  in
      uu____19866.FStar_Syntax_Syntax.n  in
    match uu____19865 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19870 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____19911 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19911;
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
                       let uu____19992 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____19992
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___263_19996 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___263_19996.deferred);
              univ_ineqs = (uu___263_19996.univ_ineqs);
              implicits = (uu___263_19996.implicits)
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
               let uu____20029 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____20029
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
            let uu___264_20052 = g  in
            let uu____20053 =
              let uu____20054 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____20054  in
            {
              guard_f = uu____20053;
              deferred = (uu___264_20052.deferred);
              univ_ineqs = (uu___264_20052.univ_ineqs);
              implicits = (uu___264_20052.implicits)
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
            let uu____20092 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____20092 with
            | FStar_Pervasives_Native.Some
                (uu____20117::(tm,uu____20119)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____20183 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____20201 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____20201;
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
                    let uu___265_20236 = trivial_guard  in
                    {
                      guard_f = (uu___265_20236.guard_f);
                      deferred = (uu___265_20236.deferred);
                      univ_ineqs = (uu___265_20236.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____20253  -> ());
    push = (fun uu____20255  -> ());
    pop = (fun uu____20257  -> ());
    snapshot =
      (fun uu____20259  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____20268  -> fun uu____20269  -> ());
    encode_modul = (fun uu____20280  -> fun uu____20281  -> ());
    encode_sig = (fun uu____20284  -> fun uu____20285  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____20291 =
             let uu____20298 = FStar_Options.peek ()  in (e, g, uu____20298)
              in
           [uu____20291]);
    solve = (fun uu____20314  -> fun uu____20315  -> fun uu____20316  -> ());
    finish = (fun uu____20322  -> ());
    refresh = (fun uu____20324  -> ())
  } 