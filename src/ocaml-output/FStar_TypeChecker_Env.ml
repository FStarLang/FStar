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
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
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
      | ((formals,t),uu____11032) ->
          let vs = mk_univ_subst formals us  in
          let uu____11056 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11056)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___221_11072  ->
    match uu___221_11072 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11098  -> new_u_univ ()))
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
      let uu____11117 = inst_tscheme t  in
      match uu____11117 with
      | (us,t1) ->
          let uu____11128 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11128)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11148  ->
          match uu____11148 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11169 =
                         let uu____11170 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____11171 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____11172 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____11173 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11170 uu____11171 uu____11172 uu____11173
                          in
                       failwith uu____11169)
                    else ();
                    (let uu____11175 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____11175))
               | uu____11184 ->
                   let uu____11185 =
                     let uu____11186 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____11186
                      in
                   failwith uu____11185)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____11192 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11198 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11204 -> false
  
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
             | ([],uu____11246) -> Maybe
             | (uu____11253,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____11272 -> No  in
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
          let uu____11363 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____11363 with
          | FStar_Pervasives_Native.None  ->
              let uu____11386 =
                FStar_Util.find_map env.gamma
                  (fun uu___222_11430  ->
                     match uu___222_11430 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11469 = FStar_Ident.lid_equals lid l  in
                         if uu____11469
                         then
                           let uu____11490 =
                             let uu____11509 =
                               let uu____11524 = inst_tscheme t  in
                               FStar_Util.Inl uu____11524  in
                             let uu____11539 = FStar_Ident.range_of_lid l  in
                             (uu____11509, uu____11539)  in
                           FStar_Pervasives_Native.Some uu____11490
                         else FStar_Pervasives_Native.None
                     | uu____11591 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11386
                (fun uu____11629  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___223_11638  ->
                        match uu___223_11638 with
                        | (uu____11641,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11643);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11644;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11645;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11646;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11647;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11667 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11667
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
                                  uu____11715 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11722 -> cache t  in
                            let uu____11723 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11723 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11729 =
                                   let uu____11730 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11730)
                                    in
                                 maybe_cache uu____11729)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11798 = find_in_sigtab env lid  in
         match uu____11798 with
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
      let uu____11878 = lookup_qname env lid  in
      match uu____11878 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____11899,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____12010 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____12010 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____12052 =
          let uu____12055 = lookup_attr env1 attr  in se1 :: uu____12055  in
        FStar_Util.smap_add (attrtab env1) attr uu____12052  in
      FStar_List.iter
        (fun attr  ->
           let uu____12065 =
             let uu____12066 = FStar_Syntax_Subst.compress attr  in
             uu____12066.FStar_Syntax_Syntax.n  in
           match uu____12065 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____12070 =
                 let uu____12071 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____12071.FStar_Ident.str  in
               add_one1 env se uu____12070
           | uu____12072 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12094) ->
          add_sigelts env ses
      | uu____12103 ->
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
            | uu____12118 -> ()))

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
        (fun uu___224_12149  ->
           match uu___224_12149 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12167 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____12228,lb::[]),uu____12230) ->
            let uu____12237 =
              let uu____12246 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____12255 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____12246, uu____12255)  in
            FStar_Pervasives_Native.Some uu____12237
        | FStar_Syntax_Syntax.Sig_let ((uu____12268,lbs),uu____12270) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____12300 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____12312 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____12312
                     then
                       let uu____12323 =
                         let uu____12332 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____12341 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____12332, uu____12341)  in
                       FStar_Pervasives_Native.Some uu____12323
                     else FStar_Pervasives_Native.None)
        | uu____12363 -> FStar_Pervasives_Native.None
  
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
          let uu____12422 =
            let uu____12431 =
              let uu____12436 =
                let uu____12437 =
                  let uu____12440 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____12440
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____12437)  in
              inst_tscheme1 uu____12436  in
            (uu____12431, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12422
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____12462,uu____12463) ->
          let uu____12468 =
            let uu____12477 =
              let uu____12482 =
                let uu____12483 =
                  let uu____12486 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____12486  in
                (us, uu____12483)  in
              inst_tscheme1 uu____12482  in
            (uu____12477, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12468
      | uu____12505 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12593 =
          match uu____12593 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12689,uvs,t,uu____12692,uu____12693,uu____12694);
                      FStar_Syntax_Syntax.sigrng = uu____12695;
                      FStar_Syntax_Syntax.sigquals = uu____12696;
                      FStar_Syntax_Syntax.sigmeta = uu____12697;
                      FStar_Syntax_Syntax.sigattrs = uu____12698;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12719 =
                     let uu____12728 = inst_tscheme1 (uvs, t)  in
                     (uu____12728, rng)  in
                   FStar_Pervasives_Native.Some uu____12719
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12752;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12754;
                      FStar_Syntax_Syntax.sigattrs = uu____12755;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12772 =
                     let uu____12773 = in_cur_mod env l  in uu____12773 = Yes
                      in
                   if uu____12772
                   then
                     let uu____12784 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12784
                      then
                        let uu____12797 =
                          let uu____12806 = inst_tscheme1 (uvs, t)  in
                          (uu____12806, rng)  in
                        FStar_Pervasives_Native.Some uu____12797
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12837 =
                        let uu____12846 = inst_tscheme1 (uvs, t)  in
                        (uu____12846, rng)  in
                      FStar_Pervasives_Native.Some uu____12837)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12871,uu____12872);
                      FStar_Syntax_Syntax.sigrng = uu____12873;
                      FStar_Syntax_Syntax.sigquals = uu____12874;
                      FStar_Syntax_Syntax.sigmeta = uu____12875;
                      FStar_Syntax_Syntax.sigattrs = uu____12876;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12917 =
                          let uu____12926 = inst_tscheme1 (uvs, k)  in
                          (uu____12926, rng)  in
                        FStar_Pervasives_Native.Some uu____12917
                    | uu____12947 ->
                        let uu____12948 =
                          let uu____12957 =
                            let uu____12962 =
                              let uu____12963 =
                                let uu____12966 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12966
                                 in
                              (uvs, uu____12963)  in
                            inst_tscheme1 uu____12962  in
                          (uu____12957, rng)  in
                        FStar_Pervasives_Native.Some uu____12948)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12989,uu____12990);
                      FStar_Syntax_Syntax.sigrng = uu____12991;
                      FStar_Syntax_Syntax.sigquals = uu____12992;
                      FStar_Syntax_Syntax.sigmeta = uu____12993;
                      FStar_Syntax_Syntax.sigattrs = uu____12994;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13036 =
                          let uu____13045 = inst_tscheme_with (uvs, k) us  in
                          (uu____13045, rng)  in
                        FStar_Pervasives_Native.Some uu____13036
                    | uu____13066 ->
                        let uu____13067 =
                          let uu____13076 =
                            let uu____13081 =
                              let uu____13082 =
                                let uu____13085 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13085
                                 in
                              (uvs, uu____13082)  in
                            inst_tscheme_with uu____13081 us  in
                          (uu____13076, rng)  in
                        FStar_Pervasives_Native.Some uu____13067)
               | FStar_Util.Inr se ->
                   let uu____13121 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13142;
                          FStar_Syntax_Syntax.sigrng = uu____13143;
                          FStar_Syntax_Syntax.sigquals = uu____13144;
                          FStar_Syntax_Syntax.sigmeta = uu____13145;
                          FStar_Syntax_Syntax.sigattrs = uu____13146;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13161 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____13121
                     (FStar_Util.map_option
                        (fun uu____13209  ->
                           match uu____13209 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____13240 =
          let uu____13251 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____13251 mapper  in
        match uu____13240 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____13325 =
              let uu____13336 =
                let uu____13343 =
                  let uu___244_13346 = t  in
                  let uu____13347 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___244_13346.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____13347;
                    FStar_Syntax_Syntax.vars =
                      (uu___244_13346.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____13343)  in
              (uu____13336, r)  in
            FStar_Pervasives_Native.Some uu____13325
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13394 = lookup_qname env l  in
      match uu____13394 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____13413 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____13465 = try_lookup_bv env bv  in
      match uu____13465 with
      | FStar_Pervasives_Native.None  ->
          let uu____13480 = variable_not_found bv  in
          FStar_Errors.raise_error uu____13480 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____13495 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____13496 =
            let uu____13497 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____13497  in
          (uu____13495, uu____13496)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____13518 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____13518 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____13584 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____13584  in
          let uu____13585 =
            let uu____13594 =
              let uu____13599 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13599)  in
            (uu____13594, r1)  in
          FStar_Pervasives_Native.Some uu____13585
  
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
        let uu____13633 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13633 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13666,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13691 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13691  in
            let uu____13692 =
              let uu____13697 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13697, r1)  in
            FStar_Pervasives_Native.Some uu____13692
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13720 = try_lookup_lid env l  in
      match uu____13720 with
      | FStar_Pervasives_Native.None  ->
          let uu____13747 = name_not_found l  in
          let uu____13752 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13747 uu____13752
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___225_13792  ->
              match uu___225_13792 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13794 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13813 = lookup_qname env lid  in
      match uu____13813 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13822,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13825;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13827;
              FStar_Syntax_Syntax.sigattrs = uu____13828;_},FStar_Pervasives_Native.None
            ),uu____13829)
          ->
          let uu____13878 =
            let uu____13885 =
              let uu____13886 =
                let uu____13889 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13889 t  in
              (uvs, uu____13886)  in
            (uu____13885, q)  in
          FStar_Pervasives_Native.Some uu____13878
      | uu____13902 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13923 = lookup_qname env lid  in
      match uu____13923 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13928,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13931;
              FStar_Syntax_Syntax.sigquals = uu____13932;
              FStar_Syntax_Syntax.sigmeta = uu____13933;
              FStar_Syntax_Syntax.sigattrs = uu____13934;_},FStar_Pervasives_Native.None
            ),uu____13935)
          ->
          let uu____13984 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13984 (uvs, t)
      | uu____13989 ->
          let uu____13990 = name_not_found lid  in
          let uu____13995 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13990 uu____13995
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14014 = lookup_qname env lid  in
      match uu____14014 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14019,uvs,t,uu____14022,uu____14023,uu____14024);
              FStar_Syntax_Syntax.sigrng = uu____14025;
              FStar_Syntax_Syntax.sigquals = uu____14026;
              FStar_Syntax_Syntax.sigmeta = uu____14027;
              FStar_Syntax_Syntax.sigattrs = uu____14028;_},FStar_Pervasives_Native.None
            ),uu____14029)
          ->
          let uu____14082 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14082 (uvs, t)
      | uu____14087 ->
          let uu____14088 = name_not_found lid  in
          let uu____14093 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14088 uu____14093
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14114 = lookup_qname env lid  in
      match uu____14114 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14121,uu____14122,uu____14123,uu____14124,uu____14125,dcs);
              FStar_Syntax_Syntax.sigrng = uu____14127;
              FStar_Syntax_Syntax.sigquals = uu____14128;
              FStar_Syntax_Syntax.sigmeta = uu____14129;
              FStar_Syntax_Syntax.sigattrs = uu____14130;_},uu____14131),uu____14132)
          -> (true, dcs)
      | uu____14193 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____14206 = lookup_qname env lid  in
      match uu____14206 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14207,uu____14208,uu____14209,l,uu____14211,uu____14212);
              FStar_Syntax_Syntax.sigrng = uu____14213;
              FStar_Syntax_Syntax.sigquals = uu____14214;
              FStar_Syntax_Syntax.sigmeta = uu____14215;
              FStar_Syntax_Syntax.sigattrs = uu____14216;_},uu____14217),uu____14218)
          -> l
      | uu____14273 ->
          let uu____14274 =
            let uu____14275 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____14275  in
          failwith uu____14274
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14324)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____14375,lbs),uu____14377)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____14399 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____14399
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____14431 -> FStar_Pervasives_Native.None)
        | uu____14436 -> FStar_Pervasives_Native.None
  
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
        let uu____14466 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____14466
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14491),uu____14492) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____14541 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14562),uu____14563) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____14612 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14633 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____14633
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____14652 = lookup_qname env ftv  in
      match uu____14652 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14656) ->
          let uu____14701 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14701 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14722,t),r) ->
               let uu____14737 =
                 let uu____14738 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14738 t  in
               FStar_Pervasives_Native.Some uu____14737)
      | uu____14739 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14750 = try_lookup_effect_lid env ftv  in
      match uu____14750 with
      | FStar_Pervasives_Native.None  ->
          let uu____14753 = name_not_found ftv  in
          let uu____14758 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14753 uu____14758
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
        let uu____14781 = lookup_qname env lid0  in
        match uu____14781 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14792);
                FStar_Syntax_Syntax.sigrng = uu____14793;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14795;
                FStar_Syntax_Syntax.sigattrs = uu____14796;_},FStar_Pervasives_Native.None
              ),uu____14797)
            ->
            let lid1 =
              let uu____14851 =
                let uu____14852 = FStar_Ident.range_of_lid lid  in
                let uu____14853 =
                  let uu____14854 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14854  in
                FStar_Range.set_use_range uu____14852 uu____14853  in
              FStar_Ident.set_lid_range lid uu____14851  in
            let uu____14855 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___226_14859  ->
                      match uu___226_14859 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14860 -> false))
               in
            if uu____14855
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14874 =
                      let uu____14875 =
                        let uu____14876 = get_range env  in
                        FStar_Range.string_of_range uu____14876  in
                      let uu____14877 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14878 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14875 uu____14877 uu____14878
                       in
                    failwith uu____14874)
                  in
               match (binders, univs1) with
               | ([],uu____14895) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14920,uu____14921::uu____14922::uu____14923) ->
                   let uu____14944 =
                     let uu____14945 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14946 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14945 uu____14946
                      in
                   failwith uu____14944
               | uu____14953 ->
                   let uu____14968 =
                     let uu____14973 =
                       let uu____14974 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14974)  in
                     inst_tscheme_with uu____14973 insts  in
                   (match uu____14968 with
                    | (uu____14987,t) ->
                        let t1 =
                          let uu____14990 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14990 t  in
                        let uu____14991 =
                          let uu____14992 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14992.FStar_Syntax_Syntax.n  in
                        (match uu____14991 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____15027 -> failwith "Impossible")))
        | uu____15034 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____15057 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____15057 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____15070,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____15077 = find1 l2  in
            (match uu____15077 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____15084 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____15084 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____15088 = find1 l  in
            (match uu____15088 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____15093 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____15093
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____15107 = lookup_qname env l1  in
      match uu____15107 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____15110;
              FStar_Syntax_Syntax.sigrng = uu____15111;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15113;
              FStar_Syntax_Syntax.sigattrs = uu____15114;_},uu____15115),uu____15116)
          -> q
      | uu____15167 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____15188 =
          let uu____15189 =
            let uu____15190 = FStar_Util.string_of_int i  in
            let uu____15191 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____15190 uu____15191
             in
          failwith uu____15189  in
        let uu____15192 = lookup_datacon env lid  in
        match uu____15192 with
        | (uu____15197,t) ->
            let uu____15199 =
              let uu____15200 = FStar_Syntax_Subst.compress t  in
              uu____15200.FStar_Syntax_Syntax.n  in
            (match uu____15199 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15204) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____15245 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____15245
                      FStar_Pervasives_Native.fst)
             | uu____15256 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15267 = lookup_qname env l  in
      match uu____15267 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15268,uu____15269,uu____15270);
              FStar_Syntax_Syntax.sigrng = uu____15271;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15273;
              FStar_Syntax_Syntax.sigattrs = uu____15274;_},uu____15275),uu____15276)
          ->
          FStar_Util.for_some
            (fun uu___227_15329  ->
               match uu___227_15329 with
               | FStar_Syntax_Syntax.Projector uu____15330 -> true
               | uu____15335 -> false) quals
      | uu____15336 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15347 = lookup_qname env lid  in
      match uu____15347 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15348,uu____15349,uu____15350,uu____15351,uu____15352,uu____15353);
              FStar_Syntax_Syntax.sigrng = uu____15354;
              FStar_Syntax_Syntax.sigquals = uu____15355;
              FStar_Syntax_Syntax.sigmeta = uu____15356;
              FStar_Syntax_Syntax.sigattrs = uu____15357;_},uu____15358),uu____15359)
          -> true
      | uu____15414 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15425 = lookup_qname env lid  in
      match uu____15425 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15426,uu____15427,uu____15428,uu____15429,uu____15430,uu____15431);
              FStar_Syntax_Syntax.sigrng = uu____15432;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15434;
              FStar_Syntax_Syntax.sigattrs = uu____15435;_},uu____15436),uu____15437)
          ->
          FStar_Util.for_some
            (fun uu___228_15498  ->
               match uu___228_15498 with
               | FStar_Syntax_Syntax.RecordType uu____15499 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____15508 -> true
               | uu____15517 -> false) quals
      | uu____15518 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____15524,uu____15525);
            FStar_Syntax_Syntax.sigrng = uu____15526;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____15528;
            FStar_Syntax_Syntax.sigattrs = uu____15529;_},uu____15530),uu____15531)
        ->
        FStar_Util.for_some
          (fun uu___229_15588  ->
             match uu___229_15588 with
             | FStar_Syntax_Syntax.Action uu____15589 -> true
             | uu____15590 -> false) quals
    | uu____15591 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15602 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____15602
  
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
      let uu____15616 =
        let uu____15617 = FStar_Syntax_Util.un_uinst head1  in
        uu____15617.FStar_Syntax_Syntax.n  in
      match uu____15616 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____15621 ->
               true
           | uu____15622 -> false)
      | uu____15623 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15634 = lookup_qname env l  in
      match uu____15634 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____15636),uu____15637) ->
          FStar_Util.for_some
            (fun uu___230_15685  ->
               match uu___230_15685 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____15686 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____15687 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15758 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15774) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15791 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15798 ->
                 FStar_Pervasives_Native.Some true
             | uu____15815 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15816 =
        let uu____15819 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15819 mapper  in
      match uu____15816 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15869 = lookup_qname env lid  in
      match uu____15869 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15870,uu____15871,tps,uu____15873,uu____15874,uu____15875);
              FStar_Syntax_Syntax.sigrng = uu____15876;
              FStar_Syntax_Syntax.sigquals = uu____15877;
              FStar_Syntax_Syntax.sigmeta = uu____15878;
              FStar_Syntax_Syntax.sigattrs = uu____15879;_},uu____15880),uu____15881)
          -> FStar_List.length tps
      | uu____15946 ->
          let uu____15947 = name_not_found lid  in
          let uu____15952 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15947 uu____15952
  
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
           (fun uu____15996  ->
              match uu____15996 with
              | (d,uu____16004) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____16019 = effect_decl_opt env l  in
      match uu____16019 with
      | FStar_Pervasives_Native.None  ->
          let uu____16034 = name_not_found l  in
          let uu____16039 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____16034 uu____16039
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____16061  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____16080  ->
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
        let uu____16111 = FStar_Ident.lid_equals l1 l2  in
        if uu____16111
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____16119 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____16119
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____16127 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____16180  ->
                        match uu____16180 with
                        | (m1,m2,uu____16193,uu____16194,uu____16195) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____16127 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16212 =
                    let uu____16217 =
                      let uu____16218 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____16219 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____16218
                        uu____16219
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____16217)
                     in
                  FStar_Errors.raise_error uu____16212 env.range
              | FStar_Pervasives_Native.Some
                  (uu____16226,uu____16227,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____16260 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____16260
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
  'Auu____16276 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____16276)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____16305 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____16331  ->
                match uu____16331 with
                | (d,uu____16337) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____16305 with
      | FStar_Pervasives_Native.None  ->
          let uu____16348 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____16348
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____16361 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____16361 with
           | (uu____16376,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____16394)::(wp,uu____16396)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____16452 -> failwith "Impossible"))
  
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
          let uu____16507 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____16507
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____16509 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____16509
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
                  let uu____16517 = get_range env  in
                  let uu____16518 =
                    let uu____16525 =
                      let uu____16526 =
                        let uu____16543 =
                          let uu____16554 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____16554]  in
                        (null_wp, uu____16543)  in
                      FStar_Syntax_Syntax.Tm_app uu____16526  in
                    FStar_Syntax_Syntax.mk uu____16525  in
                  uu____16518 FStar_Pervasives_Native.None uu____16517  in
                let uu____16594 =
                  let uu____16595 =
                    let uu____16606 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____16606]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____16595;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____16594))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___245_16643 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___245_16643.order);
              joins = (uu___245_16643.joins)
            }  in
          let uu___246_16652 = env  in
          {
            solver = (uu___246_16652.solver);
            range = (uu___246_16652.range);
            curmodule = (uu___246_16652.curmodule);
            gamma = (uu___246_16652.gamma);
            gamma_sig = (uu___246_16652.gamma_sig);
            gamma_cache = (uu___246_16652.gamma_cache);
            modules = (uu___246_16652.modules);
            expected_typ = (uu___246_16652.expected_typ);
            sigtab = (uu___246_16652.sigtab);
            attrtab = (uu___246_16652.attrtab);
            is_pattern = (uu___246_16652.is_pattern);
            instantiate_imp = (uu___246_16652.instantiate_imp);
            effects;
            generalize = (uu___246_16652.generalize);
            letrecs = (uu___246_16652.letrecs);
            top_level = (uu___246_16652.top_level);
            check_uvars = (uu___246_16652.check_uvars);
            use_eq = (uu___246_16652.use_eq);
            is_iface = (uu___246_16652.is_iface);
            admit = (uu___246_16652.admit);
            lax = (uu___246_16652.lax);
            lax_universes = (uu___246_16652.lax_universes);
            phase1 = (uu___246_16652.phase1);
            failhard = (uu___246_16652.failhard);
            nosynth = (uu___246_16652.nosynth);
            uvar_subtyping = (uu___246_16652.uvar_subtyping);
            tc_term = (uu___246_16652.tc_term);
            type_of = (uu___246_16652.type_of);
            universe_of = (uu___246_16652.universe_of);
            check_type_of = (uu___246_16652.check_type_of);
            use_bv_sorts = (uu___246_16652.use_bv_sorts);
            qtbl_name_and_index = (uu___246_16652.qtbl_name_and_index);
            normalized_eff_names = (uu___246_16652.normalized_eff_names);
            proof_ns = (uu___246_16652.proof_ns);
            synth_hook = (uu___246_16652.synth_hook);
            splice = (uu___246_16652.splice);
            is_native_tactic = (uu___246_16652.is_native_tactic);
            identifier_info = (uu___246_16652.identifier_info);
            tc_hooks = (uu___246_16652.tc_hooks);
            dsenv = (uu___246_16652.dsenv);
            dep_graph = (uu___246_16652.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____16682 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____16682  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16840 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16841 = l1 u t wp e  in
                                l2 u t uu____16840 uu____16841))
                | uu____16842 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16914 = inst_tscheme_with lift_t [u]  in
            match uu____16914 with
            | (uu____16921,lift_t1) ->
                let uu____16923 =
                  let uu____16930 =
                    let uu____16931 =
                      let uu____16948 =
                        let uu____16959 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16968 =
                          let uu____16979 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16979]  in
                        uu____16959 :: uu____16968  in
                      (lift_t1, uu____16948)  in
                    FStar_Syntax_Syntax.Tm_app uu____16931  in
                  FStar_Syntax_Syntax.mk uu____16930  in
                uu____16923 FStar_Pervasives_Native.None
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
            let uu____17091 = inst_tscheme_with lift_t [u]  in
            match uu____17091 with
            | (uu____17098,lift_t1) ->
                let uu____17100 =
                  let uu____17107 =
                    let uu____17108 =
                      let uu____17125 =
                        let uu____17136 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17145 =
                          let uu____17156 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____17165 =
                            let uu____17176 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____17176]  in
                          uu____17156 :: uu____17165  in
                        uu____17136 :: uu____17145  in
                      (lift_t1, uu____17125)  in
                    FStar_Syntax_Syntax.Tm_app uu____17108  in
                  FStar_Syntax_Syntax.mk uu____17107  in
                uu____17100 FStar_Pervasives_Native.None
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
              let uu____17278 =
                let uu____17279 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____17279
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____17278  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____17283 =
              let uu____17284 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____17284  in
            let uu____17285 =
              let uu____17286 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____17312 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____17312)
                 in
              FStar_Util.dflt "none" uu____17286  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____17283
              uu____17285
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____17338  ->
                    match uu____17338 with
                    | (e,uu____17346) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____17369 =
            match uu____17369 with
            | (i,j) ->
                let uu____17380 = FStar_Ident.lid_equals i j  in
                if uu____17380
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
              let uu____17412 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____17422 = FStar_Ident.lid_equals i k  in
                        if uu____17422
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____17433 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____17433
                                  then []
                                  else
                                    (let uu____17437 =
                                       let uu____17446 =
                                         find_edge order1 (i, k)  in
                                       let uu____17449 =
                                         find_edge order1 (k, j)  in
                                       (uu____17446, uu____17449)  in
                                     match uu____17437 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____17464 =
                                           compose_edges e1 e2  in
                                         [uu____17464]
                                     | uu____17465 -> [])))))
                 in
              FStar_List.append order1 uu____17412  in
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
                   let uu____17495 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____17497 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____17497
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____17495
                   then
                     let uu____17502 =
                       let uu____17507 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____17507)
                        in
                     let uu____17508 = get_range env  in
                     FStar_Errors.raise_error uu____17502 uu____17508
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____17585 = FStar_Ident.lid_equals i j
                                   in
                                if uu____17585
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____17634 =
                                              let uu____17643 =
                                                find_edge order2 (i, k)  in
                                              let uu____17646 =
                                                find_edge order2 (j, k)  in
                                              (uu____17643, uu____17646)  in
                                            match uu____17634 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____17688,uu____17689)
                                                     ->
                                                     let uu____17696 =
                                                       let uu____17701 =
                                                         let uu____17702 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17702
                                                          in
                                                       let uu____17705 =
                                                         let uu____17706 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17706
                                                          in
                                                       (uu____17701,
                                                         uu____17705)
                                                        in
                                                     (match uu____17696 with
                                                      | (true ,true ) ->
                                                          let uu____17717 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____17717
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
                                            | uu____17742 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___247_17815 = env.effects  in
              { decls = (uu___247_17815.decls); order = order2; joins }  in
            let uu___248_17816 = env  in
            {
              solver = (uu___248_17816.solver);
              range = (uu___248_17816.range);
              curmodule = (uu___248_17816.curmodule);
              gamma = (uu___248_17816.gamma);
              gamma_sig = (uu___248_17816.gamma_sig);
              gamma_cache = (uu___248_17816.gamma_cache);
              modules = (uu___248_17816.modules);
              expected_typ = (uu___248_17816.expected_typ);
              sigtab = (uu___248_17816.sigtab);
              attrtab = (uu___248_17816.attrtab);
              is_pattern = (uu___248_17816.is_pattern);
              instantiate_imp = (uu___248_17816.instantiate_imp);
              effects;
              generalize = (uu___248_17816.generalize);
              letrecs = (uu___248_17816.letrecs);
              top_level = (uu___248_17816.top_level);
              check_uvars = (uu___248_17816.check_uvars);
              use_eq = (uu___248_17816.use_eq);
              is_iface = (uu___248_17816.is_iface);
              admit = (uu___248_17816.admit);
              lax = (uu___248_17816.lax);
              lax_universes = (uu___248_17816.lax_universes);
              phase1 = (uu___248_17816.phase1);
              failhard = (uu___248_17816.failhard);
              nosynth = (uu___248_17816.nosynth);
              uvar_subtyping = (uu___248_17816.uvar_subtyping);
              tc_term = (uu___248_17816.tc_term);
              type_of = (uu___248_17816.type_of);
              universe_of = (uu___248_17816.universe_of);
              check_type_of = (uu___248_17816.check_type_of);
              use_bv_sorts = (uu___248_17816.use_bv_sorts);
              qtbl_name_and_index = (uu___248_17816.qtbl_name_and_index);
              normalized_eff_names = (uu___248_17816.normalized_eff_names);
              proof_ns = (uu___248_17816.proof_ns);
              synth_hook = (uu___248_17816.synth_hook);
              splice = (uu___248_17816.splice);
              is_native_tactic = (uu___248_17816.is_native_tactic);
              identifier_info = (uu___248_17816.identifier_info);
              tc_hooks = (uu___248_17816.tc_hooks);
              dsenv = (uu___248_17816.dsenv);
              dep_graph = (uu___248_17816.dep_graph)
            }))
      | uu____17817 -> env
  
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
        | uu____17845 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17857 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17857 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17874 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17874 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17896 =
                     let uu____17901 =
                       let uu____17902 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17909 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17918 =
                         let uu____17919 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17919  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17902 uu____17909 uu____17918
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17901)
                      in
                   FStar_Errors.raise_error uu____17896
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17924 =
                     let uu____17935 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17935 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17972  ->
                        fun uu____17973  ->
                          match (uu____17972, uu____17973) with
                          | ((x,uu____18003),(t,uu____18005)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17924
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____18036 =
                     let uu___249_18037 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___249_18037.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___249_18037.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___249_18037.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___249_18037.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____18036
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
          let uu____18067 = effect_decl_opt env effect_name  in
          match uu____18067 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____18100 =
                only_reifiable &&
                  (let uu____18102 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____18102)
                 in
              if uu____18100
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____18118 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____18141 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____18178 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____18178
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____18179 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____18179
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____18193 =
                       let uu____18196 = get_range env  in
                       let uu____18197 =
                         let uu____18204 =
                           let uu____18205 =
                             let uu____18222 =
                               let uu____18233 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____18233; wp]  in
                             (repr, uu____18222)  in
                           FStar_Syntax_Syntax.Tm_app uu____18205  in
                         FStar_Syntax_Syntax.mk uu____18204  in
                       uu____18197 FStar_Pervasives_Native.None uu____18196
                        in
                     FStar_Pervasives_Native.Some uu____18193)
  
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
          let uu____18323 =
            let uu____18328 =
              let uu____18329 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____18329
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____18328)  in
          let uu____18330 = get_range env  in
          FStar_Errors.raise_error uu____18323 uu____18330  in
        let uu____18331 = effect_repr_aux true env c u_c  in
        match uu____18331 with
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
      | uu____18377 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____18388 =
        let uu____18389 = FStar_Syntax_Subst.compress t  in
        uu____18389.FStar_Syntax_Syntax.n  in
      match uu____18388 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____18392,c) ->
          is_reifiable_comp env c
      | uu____18414 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___250_18435 = env  in
        {
          solver = (uu___250_18435.solver);
          range = (uu___250_18435.range);
          curmodule = (uu___250_18435.curmodule);
          gamma = (uu___250_18435.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___250_18435.gamma_cache);
          modules = (uu___250_18435.modules);
          expected_typ = (uu___250_18435.expected_typ);
          sigtab = (uu___250_18435.sigtab);
          attrtab = (uu___250_18435.attrtab);
          is_pattern = (uu___250_18435.is_pattern);
          instantiate_imp = (uu___250_18435.instantiate_imp);
          effects = (uu___250_18435.effects);
          generalize = (uu___250_18435.generalize);
          letrecs = (uu___250_18435.letrecs);
          top_level = (uu___250_18435.top_level);
          check_uvars = (uu___250_18435.check_uvars);
          use_eq = (uu___250_18435.use_eq);
          is_iface = (uu___250_18435.is_iface);
          admit = (uu___250_18435.admit);
          lax = (uu___250_18435.lax);
          lax_universes = (uu___250_18435.lax_universes);
          phase1 = (uu___250_18435.phase1);
          failhard = (uu___250_18435.failhard);
          nosynth = (uu___250_18435.nosynth);
          uvar_subtyping = (uu___250_18435.uvar_subtyping);
          tc_term = (uu___250_18435.tc_term);
          type_of = (uu___250_18435.type_of);
          universe_of = (uu___250_18435.universe_of);
          check_type_of = (uu___250_18435.check_type_of);
          use_bv_sorts = (uu___250_18435.use_bv_sorts);
          qtbl_name_and_index = (uu___250_18435.qtbl_name_and_index);
          normalized_eff_names = (uu___250_18435.normalized_eff_names);
          proof_ns = (uu___250_18435.proof_ns);
          synth_hook = (uu___250_18435.synth_hook);
          splice = (uu___250_18435.splice);
          is_native_tactic = (uu___250_18435.is_native_tactic);
          identifier_info = (uu___250_18435.identifier_info);
          tc_hooks = (uu___250_18435.tc_hooks);
          dsenv = (uu___250_18435.dsenv);
          dep_graph = (uu___250_18435.dep_graph)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___251_18448 = env  in
      {
        solver = (uu___251_18448.solver);
        range = (uu___251_18448.range);
        curmodule = (uu___251_18448.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___251_18448.gamma_sig);
        gamma_cache = (uu___251_18448.gamma_cache);
        modules = (uu___251_18448.modules);
        expected_typ = (uu___251_18448.expected_typ);
        sigtab = (uu___251_18448.sigtab);
        attrtab = (uu___251_18448.attrtab);
        is_pattern = (uu___251_18448.is_pattern);
        instantiate_imp = (uu___251_18448.instantiate_imp);
        effects = (uu___251_18448.effects);
        generalize = (uu___251_18448.generalize);
        letrecs = (uu___251_18448.letrecs);
        top_level = (uu___251_18448.top_level);
        check_uvars = (uu___251_18448.check_uvars);
        use_eq = (uu___251_18448.use_eq);
        is_iface = (uu___251_18448.is_iface);
        admit = (uu___251_18448.admit);
        lax = (uu___251_18448.lax);
        lax_universes = (uu___251_18448.lax_universes);
        phase1 = (uu___251_18448.phase1);
        failhard = (uu___251_18448.failhard);
        nosynth = (uu___251_18448.nosynth);
        uvar_subtyping = (uu___251_18448.uvar_subtyping);
        tc_term = (uu___251_18448.tc_term);
        type_of = (uu___251_18448.type_of);
        universe_of = (uu___251_18448.universe_of);
        check_type_of = (uu___251_18448.check_type_of);
        use_bv_sorts = (uu___251_18448.use_bv_sorts);
        qtbl_name_and_index = (uu___251_18448.qtbl_name_and_index);
        normalized_eff_names = (uu___251_18448.normalized_eff_names);
        proof_ns = (uu___251_18448.proof_ns);
        synth_hook = (uu___251_18448.synth_hook);
        splice = (uu___251_18448.splice);
        is_native_tactic = (uu___251_18448.is_native_tactic);
        identifier_info = (uu___251_18448.identifier_info);
        tc_hooks = (uu___251_18448.tc_hooks);
        dsenv = (uu___251_18448.dsenv);
        dep_graph = (uu___251_18448.dep_graph)
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
            (let uu___252_18503 = env  in
             {
               solver = (uu___252_18503.solver);
               range = (uu___252_18503.range);
               curmodule = (uu___252_18503.curmodule);
               gamma = rest;
               gamma_sig = (uu___252_18503.gamma_sig);
               gamma_cache = (uu___252_18503.gamma_cache);
               modules = (uu___252_18503.modules);
               expected_typ = (uu___252_18503.expected_typ);
               sigtab = (uu___252_18503.sigtab);
               attrtab = (uu___252_18503.attrtab);
               is_pattern = (uu___252_18503.is_pattern);
               instantiate_imp = (uu___252_18503.instantiate_imp);
               effects = (uu___252_18503.effects);
               generalize = (uu___252_18503.generalize);
               letrecs = (uu___252_18503.letrecs);
               top_level = (uu___252_18503.top_level);
               check_uvars = (uu___252_18503.check_uvars);
               use_eq = (uu___252_18503.use_eq);
               is_iface = (uu___252_18503.is_iface);
               admit = (uu___252_18503.admit);
               lax = (uu___252_18503.lax);
               lax_universes = (uu___252_18503.lax_universes);
               phase1 = (uu___252_18503.phase1);
               failhard = (uu___252_18503.failhard);
               nosynth = (uu___252_18503.nosynth);
               uvar_subtyping = (uu___252_18503.uvar_subtyping);
               tc_term = (uu___252_18503.tc_term);
               type_of = (uu___252_18503.type_of);
               universe_of = (uu___252_18503.universe_of);
               check_type_of = (uu___252_18503.check_type_of);
               use_bv_sorts = (uu___252_18503.use_bv_sorts);
               qtbl_name_and_index = (uu___252_18503.qtbl_name_and_index);
               normalized_eff_names = (uu___252_18503.normalized_eff_names);
               proof_ns = (uu___252_18503.proof_ns);
               synth_hook = (uu___252_18503.synth_hook);
               splice = (uu___252_18503.splice);
               is_native_tactic = (uu___252_18503.is_native_tactic);
               identifier_info = (uu___252_18503.identifier_info);
               tc_hooks = (uu___252_18503.tc_hooks);
               dsenv = (uu___252_18503.dsenv);
               dep_graph = (uu___252_18503.dep_graph)
             }))
    | uu____18504 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____18532  ->
             match uu____18532 with | (x,uu____18540) -> push_bv env1 x) env
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
            let uu___253_18574 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___253_18574.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___253_18574.FStar_Syntax_Syntax.index);
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
      (let uu___254_18614 = env  in
       {
         solver = (uu___254_18614.solver);
         range = (uu___254_18614.range);
         curmodule = (uu___254_18614.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___254_18614.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___254_18614.sigtab);
         attrtab = (uu___254_18614.attrtab);
         is_pattern = (uu___254_18614.is_pattern);
         instantiate_imp = (uu___254_18614.instantiate_imp);
         effects = (uu___254_18614.effects);
         generalize = (uu___254_18614.generalize);
         letrecs = (uu___254_18614.letrecs);
         top_level = (uu___254_18614.top_level);
         check_uvars = (uu___254_18614.check_uvars);
         use_eq = (uu___254_18614.use_eq);
         is_iface = (uu___254_18614.is_iface);
         admit = (uu___254_18614.admit);
         lax = (uu___254_18614.lax);
         lax_universes = (uu___254_18614.lax_universes);
         phase1 = (uu___254_18614.phase1);
         failhard = (uu___254_18614.failhard);
         nosynth = (uu___254_18614.nosynth);
         uvar_subtyping = (uu___254_18614.uvar_subtyping);
         tc_term = (uu___254_18614.tc_term);
         type_of = (uu___254_18614.type_of);
         universe_of = (uu___254_18614.universe_of);
         check_type_of = (uu___254_18614.check_type_of);
         use_bv_sorts = (uu___254_18614.use_bv_sorts);
         qtbl_name_and_index = (uu___254_18614.qtbl_name_and_index);
         normalized_eff_names = (uu___254_18614.normalized_eff_names);
         proof_ns = (uu___254_18614.proof_ns);
         synth_hook = (uu___254_18614.synth_hook);
         splice = (uu___254_18614.splice);
         is_native_tactic = (uu___254_18614.is_native_tactic);
         identifier_info = (uu___254_18614.identifier_info);
         tc_hooks = (uu___254_18614.tc_hooks);
         dsenv = (uu___254_18614.dsenv);
         dep_graph = (uu___254_18614.dep_graph)
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
        let uu____18656 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____18656 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____18684 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____18684)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___255_18699 = env  in
      {
        solver = (uu___255_18699.solver);
        range = (uu___255_18699.range);
        curmodule = (uu___255_18699.curmodule);
        gamma = (uu___255_18699.gamma);
        gamma_sig = (uu___255_18699.gamma_sig);
        gamma_cache = (uu___255_18699.gamma_cache);
        modules = (uu___255_18699.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___255_18699.sigtab);
        attrtab = (uu___255_18699.attrtab);
        is_pattern = (uu___255_18699.is_pattern);
        instantiate_imp = (uu___255_18699.instantiate_imp);
        effects = (uu___255_18699.effects);
        generalize = (uu___255_18699.generalize);
        letrecs = (uu___255_18699.letrecs);
        top_level = (uu___255_18699.top_level);
        check_uvars = (uu___255_18699.check_uvars);
        use_eq = false;
        is_iface = (uu___255_18699.is_iface);
        admit = (uu___255_18699.admit);
        lax = (uu___255_18699.lax);
        lax_universes = (uu___255_18699.lax_universes);
        phase1 = (uu___255_18699.phase1);
        failhard = (uu___255_18699.failhard);
        nosynth = (uu___255_18699.nosynth);
        uvar_subtyping = (uu___255_18699.uvar_subtyping);
        tc_term = (uu___255_18699.tc_term);
        type_of = (uu___255_18699.type_of);
        universe_of = (uu___255_18699.universe_of);
        check_type_of = (uu___255_18699.check_type_of);
        use_bv_sorts = (uu___255_18699.use_bv_sorts);
        qtbl_name_and_index = (uu___255_18699.qtbl_name_and_index);
        normalized_eff_names = (uu___255_18699.normalized_eff_names);
        proof_ns = (uu___255_18699.proof_ns);
        synth_hook = (uu___255_18699.synth_hook);
        splice = (uu___255_18699.splice);
        is_native_tactic = (uu___255_18699.is_native_tactic);
        identifier_info = (uu___255_18699.identifier_info);
        tc_hooks = (uu___255_18699.tc_hooks);
        dsenv = (uu___255_18699.dsenv);
        dep_graph = (uu___255_18699.dep_graph)
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
    let uu____18727 = expected_typ env_  in
    ((let uu___256_18733 = env_  in
      {
        solver = (uu___256_18733.solver);
        range = (uu___256_18733.range);
        curmodule = (uu___256_18733.curmodule);
        gamma = (uu___256_18733.gamma);
        gamma_sig = (uu___256_18733.gamma_sig);
        gamma_cache = (uu___256_18733.gamma_cache);
        modules = (uu___256_18733.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___256_18733.sigtab);
        attrtab = (uu___256_18733.attrtab);
        is_pattern = (uu___256_18733.is_pattern);
        instantiate_imp = (uu___256_18733.instantiate_imp);
        effects = (uu___256_18733.effects);
        generalize = (uu___256_18733.generalize);
        letrecs = (uu___256_18733.letrecs);
        top_level = (uu___256_18733.top_level);
        check_uvars = (uu___256_18733.check_uvars);
        use_eq = false;
        is_iface = (uu___256_18733.is_iface);
        admit = (uu___256_18733.admit);
        lax = (uu___256_18733.lax);
        lax_universes = (uu___256_18733.lax_universes);
        phase1 = (uu___256_18733.phase1);
        failhard = (uu___256_18733.failhard);
        nosynth = (uu___256_18733.nosynth);
        uvar_subtyping = (uu___256_18733.uvar_subtyping);
        tc_term = (uu___256_18733.tc_term);
        type_of = (uu___256_18733.type_of);
        universe_of = (uu___256_18733.universe_of);
        check_type_of = (uu___256_18733.check_type_of);
        use_bv_sorts = (uu___256_18733.use_bv_sorts);
        qtbl_name_and_index = (uu___256_18733.qtbl_name_and_index);
        normalized_eff_names = (uu___256_18733.normalized_eff_names);
        proof_ns = (uu___256_18733.proof_ns);
        synth_hook = (uu___256_18733.synth_hook);
        splice = (uu___256_18733.splice);
        is_native_tactic = (uu___256_18733.is_native_tactic);
        identifier_info = (uu___256_18733.identifier_info);
        tc_hooks = (uu___256_18733.tc_hooks);
        dsenv = (uu___256_18733.dsenv);
        dep_graph = (uu___256_18733.dep_graph)
      }), uu____18727)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____18743 =
      let uu____18746 = FStar_Ident.id_of_text ""  in [uu____18746]  in
    FStar_Ident.lid_of_ids uu____18743  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____18752 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____18752
        then
          let uu____18755 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____18755 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___257_18782 = env  in
       {
         solver = (uu___257_18782.solver);
         range = (uu___257_18782.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_18782.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___257_18782.expected_typ);
         sigtab = (uu___257_18782.sigtab);
         attrtab = (uu___257_18782.attrtab);
         is_pattern = (uu___257_18782.is_pattern);
         instantiate_imp = (uu___257_18782.instantiate_imp);
         effects = (uu___257_18782.effects);
         generalize = (uu___257_18782.generalize);
         letrecs = (uu___257_18782.letrecs);
         top_level = (uu___257_18782.top_level);
         check_uvars = (uu___257_18782.check_uvars);
         use_eq = (uu___257_18782.use_eq);
         is_iface = (uu___257_18782.is_iface);
         admit = (uu___257_18782.admit);
         lax = (uu___257_18782.lax);
         lax_universes = (uu___257_18782.lax_universes);
         phase1 = (uu___257_18782.phase1);
         failhard = (uu___257_18782.failhard);
         nosynth = (uu___257_18782.nosynth);
         uvar_subtyping = (uu___257_18782.uvar_subtyping);
         tc_term = (uu___257_18782.tc_term);
         type_of = (uu___257_18782.type_of);
         universe_of = (uu___257_18782.universe_of);
         check_type_of = (uu___257_18782.check_type_of);
         use_bv_sorts = (uu___257_18782.use_bv_sorts);
         qtbl_name_and_index = (uu___257_18782.qtbl_name_and_index);
         normalized_eff_names = (uu___257_18782.normalized_eff_names);
         proof_ns = (uu___257_18782.proof_ns);
         synth_hook = (uu___257_18782.synth_hook);
         splice = (uu___257_18782.splice);
         is_native_tactic = (uu___257_18782.is_native_tactic);
         identifier_info = (uu___257_18782.identifier_info);
         tc_hooks = (uu___257_18782.tc_hooks);
         dsenv = (uu___257_18782.dsenv);
         dep_graph = (uu___257_18782.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18833)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18837,(uu____18838,t)))::tl1
          ->
          let uu____18859 =
            let uu____18862 = FStar_Syntax_Free.uvars t  in
            ext out uu____18862  in
          aux uu____18859 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18865;
            FStar_Syntax_Syntax.index = uu____18866;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18873 =
            let uu____18876 = FStar_Syntax_Free.uvars t  in
            ext out uu____18876  in
          aux uu____18873 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18933)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18937,(uu____18938,t)))::tl1
          ->
          let uu____18959 =
            let uu____18962 = FStar_Syntax_Free.univs t  in
            ext out uu____18962  in
          aux uu____18959 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18965;
            FStar_Syntax_Syntax.index = uu____18966;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18973 =
            let uu____18976 = FStar_Syntax_Free.univs t  in
            ext out uu____18976  in
          aux uu____18973 tl1
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
          let uu____19037 = FStar_Util.set_add uname out  in
          aux uu____19037 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19040,(uu____19041,t)))::tl1
          ->
          let uu____19062 =
            let uu____19065 = FStar_Syntax_Free.univnames t  in
            ext out uu____19065  in
          aux uu____19062 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19068;
            FStar_Syntax_Syntax.index = uu____19069;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19076 =
            let uu____19079 = FStar_Syntax_Free.univnames t  in
            ext out uu____19079  in
          aux uu____19076 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___231_19099  ->
            match uu___231_19099 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____19103 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____19116 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____19126 =
      let uu____19135 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____19135
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____19126 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____19179 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___232_19189  ->
              match uu___232_19189 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____19191 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____19191
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____19194) ->
                  let uu____19211 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____19211))
       in
    FStar_All.pipe_right uu____19179 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___233_19218  ->
    match uu___233_19218 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____19220 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____19220
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____19240  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____19282) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____19301,uu____19302) -> false  in
      let uu____19311 =
        FStar_List.tryFind
          (fun uu____19329  ->
             match uu____19329 with | (p,uu____19337) -> list_prefix p path)
          env.proof_ns
         in
      match uu____19311 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____19348,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19370 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____19370
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___258_19388 = e  in
        {
          solver = (uu___258_19388.solver);
          range = (uu___258_19388.range);
          curmodule = (uu___258_19388.curmodule);
          gamma = (uu___258_19388.gamma);
          gamma_sig = (uu___258_19388.gamma_sig);
          gamma_cache = (uu___258_19388.gamma_cache);
          modules = (uu___258_19388.modules);
          expected_typ = (uu___258_19388.expected_typ);
          sigtab = (uu___258_19388.sigtab);
          attrtab = (uu___258_19388.attrtab);
          is_pattern = (uu___258_19388.is_pattern);
          instantiate_imp = (uu___258_19388.instantiate_imp);
          effects = (uu___258_19388.effects);
          generalize = (uu___258_19388.generalize);
          letrecs = (uu___258_19388.letrecs);
          top_level = (uu___258_19388.top_level);
          check_uvars = (uu___258_19388.check_uvars);
          use_eq = (uu___258_19388.use_eq);
          is_iface = (uu___258_19388.is_iface);
          admit = (uu___258_19388.admit);
          lax = (uu___258_19388.lax);
          lax_universes = (uu___258_19388.lax_universes);
          phase1 = (uu___258_19388.phase1);
          failhard = (uu___258_19388.failhard);
          nosynth = (uu___258_19388.nosynth);
          uvar_subtyping = (uu___258_19388.uvar_subtyping);
          tc_term = (uu___258_19388.tc_term);
          type_of = (uu___258_19388.type_of);
          universe_of = (uu___258_19388.universe_of);
          check_type_of = (uu___258_19388.check_type_of);
          use_bv_sorts = (uu___258_19388.use_bv_sorts);
          qtbl_name_and_index = (uu___258_19388.qtbl_name_and_index);
          normalized_eff_names = (uu___258_19388.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___258_19388.synth_hook);
          splice = (uu___258_19388.splice);
          is_native_tactic = (uu___258_19388.is_native_tactic);
          identifier_info = (uu___258_19388.identifier_info);
          tc_hooks = (uu___258_19388.tc_hooks);
          dsenv = (uu___258_19388.dsenv);
          dep_graph = (uu___258_19388.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___259_19428 = e  in
      {
        solver = (uu___259_19428.solver);
        range = (uu___259_19428.range);
        curmodule = (uu___259_19428.curmodule);
        gamma = (uu___259_19428.gamma);
        gamma_sig = (uu___259_19428.gamma_sig);
        gamma_cache = (uu___259_19428.gamma_cache);
        modules = (uu___259_19428.modules);
        expected_typ = (uu___259_19428.expected_typ);
        sigtab = (uu___259_19428.sigtab);
        attrtab = (uu___259_19428.attrtab);
        is_pattern = (uu___259_19428.is_pattern);
        instantiate_imp = (uu___259_19428.instantiate_imp);
        effects = (uu___259_19428.effects);
        generalize = (uu___259_19428.generalize);
        letrecs = (uu___259_19428.letrecs);
        top_level = (uu___259_19428.top_level);
        check_uvars = (uu___259_19428.check_uvars);
        use_eq = (uu___259_19428.use_eq);
        is_iface = (uu___259_19428.is_iface);
        admit = (uu___259_19428.admit);
        lax = (uu___259_19428.lax);
        lax_universes = (uu___259_19428.lax_universes);
        phase1 = (uu___259_19428.phase1);
        failhard = (uu___259_19428.failhard);
        nosynth = (uu___259_19428.nosynth);
        uvar_subtyping = (uu___259_19428.uvar_subtyping);
        tc_term = (uu___259_19428.tc_term);
        type_of = (uu___259_19428.type_of);
        universe_of = (uu___259_19428.universe_of);
        check_type_of = (uu___259_19428.check_type_of);
        use_bv_sorts = (uu___259_19428.use_bv_sorts);
        qtbl_name_and_index = (uu___259_19428.qtbl_name_and_index);
        normalized_eff_names = (uu___259_19428.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___259_19428.synth_hook);
        splice = (uu___259_19428.splice);
        is_native_tactic = (uu___259_19428.is_native_tactic);
        identifier_info = (uu___259_19428.identifier_info);
        tc_hooks = (uu___259_19428.tc_hooks);
        dsenv = (uu___259_19428.dsenv);
        dep_graph = (uu___259_19428.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____19443 = FStar_Syntax_Free.names t  in
      let uu____19446 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____19443 uu____19446
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____19467 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____19467
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____19475 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____19475
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____19492 =
      match uu____19492 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____19502 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____19502)
       in
    let uu____19504 =
      let uu____19507 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____19507 FStar_List.rev  in
    FStar_All.pipe_right uu____19504 (FStar_String.concat " ")
  
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
                  (let uu____19560 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____19560 with
                   | FStar_Pervasives_Native.Some uu____19563 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____19564 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____19570;
        univ_ineqs = uu____19571; implicits = uu____19572;_} -> true
    | uu____19583 -> false
  
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
          let uu___260_19610 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___260_19610.deferred);
            univ_ineqs = (uu___260_19610.univ_ineqs);
            implicits = (uu___260_19610.implicits)
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
          let uu____19645 = FStar_Options.defensive ()  in
          if uu____19645
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____19649 =
              let uu____19650 =
                let uu____19651 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____19651  in
              Prims.op_Negation uu____19650  in
            (if uu____19649
             then
               let uu____19656 =
                 let uu____19661 =
                   let uu____19662 = FStar_Syntax_Print.term_to_string t  in
                   let uu____19663 =
                     let uu____19664 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____19664
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____19662 uu____19663
                    in
                 (FStar_Errors.Warning_Defensive, uu____19661)  in
               FStar_Errors.log_issue rng uu____19656
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
          let uu____19695 =
            let uu____19696 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19696  in
          if uu____19695
          then ()
          else
            (let uu____19698 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____19698 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____19721 =
            let uu____19722 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19722  in
          if uu____19721
          then ()
          else
            (let uu____19724 = bound_vars e  in
             def_check_closed_in rng msg uu____19724 t)
  
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
          let uu___261_19759 = g  in
          let uu____19760 =
            let uu____19761 =
              let uu____19762 =
                let uu____19769 =
                  let uu____19770 =
                    let uu____19787 =
                      let uu____19798 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____19798]  in
                    (f, uu____19787)  in
                  FStar_Syntax_Syntax.Tm_app uu____19770  in
                FStar_Syntax_Syntax.mk uu____19769  in
              uu____19762 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____19761
             in
          {
            guard_f = uu____19760;
            deferred = (uu___261_19759.deferred);
            univ_ineqs = (uu___261_19759.univ_ineqs);
            implicits = (uu___261_19759.implicits)
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
          let uu___262_19854 = g  in
          let uu____19855 =
            let uu____19856 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19856  in
          {
            guard_f = uu____19855;
            deferred = (uu___262_19854.deferred);
            univ_ineqs = (uu___262_19854.univ_ineqs);
            implicits = (uu___262_19854.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19862 ->
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
          let uu____19877 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19877
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19883 =
      let uu____19884 = FStar_Syntax_Util.unmeta t  in
      uu____19884.FStar_Syntax_Syntax.n  in
    match uu____19883 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19888 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____19929 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19929;
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
                       let uu____20010 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____20010
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___263_20014 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___263_20014.deferred);
              univ_ineqs = (uu___263_20014.univ_ineqs);
              implicits = (uu___263_20014.implicits)
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
               let uu____20047 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____20047
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
            let uu___264_20070 = g  in
            let uu____20071 =
              let uu____20072 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____20072  in
            {
              guard_f = uu____20071;
              deferred = (uu___264_20070.deferred);
              univ_ineqs = (uu___264_20070.univ_ineqs);
              implicits = (uu___264_20070.implicits)
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
            let uu____20110 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____20110 with
            | FStar_Pervasives_Native.Some
                (uu____20135::(tm,uu____20137)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____20201 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____20219 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____20219;
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
                    let uu___265_20254 = trivial_guard  in
                    {
                      guard_f = (uu___265_20254.guard_f);
                      deferred = (uu___265_20254.deferred);
                      univ_ineqs = (uu___265_20254.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____20271  -> ());
    push = (fun uu____20273  -> ());
    pop = (fun uu____20275  -> ());
    snapshot =
      (fun uu____20277  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____20286  -> fun uu____20287  -> ());
    encode_modul = (fun uu____20298  -> fun uu____20299  -> ());
    encode_sig = (fun uu____20302  -> fun uu____20303  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____20309 =
             let uu____20316 = FStar_Options.peek ()  in (e, g, uu____20316)
              in
           [uu____20309]);
    solve = (fun uu____20332  -> fun uu____20333  -> fun uu____20334  -> ());
    finish = (fun uu____20340  -> ());
    refresh = (fun uu____20342  -> ())
  } 