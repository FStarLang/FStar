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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
           (fun uu___96_8271  ->
              match uu___96_8271 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____8274 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8274  in
                  let uu____8275 =
                    let uu____8276 = FStar_Syntax_Subst.compress y  in
                    uu____8276.FStar_Syntax_Syntax.n  in
                  (match uu____8275 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8280 =
                         let uu___110_8281 = y1  in
                         let uu____8282 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___110_8281.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___110_8281.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8282
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8280
                   | uu____8285 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___111_8297 = env  in
      let uu____8298 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___111_8297.solver);
        range = (uu___111_8297.range);
        curmodule = (uu___111_8297.curmodule);
        gamma = uu____8298;
        gamma_sig = (uu___111_8297.gamma_sig);
        gamma_cache = (uu___111_8297.gamma_cache);
        modules = (uu___111_8297.modules);
        expected_typ = (uu___111_8297.expected_typ);
        sigtab = (uu___111_8297.sigtab);
        is_pattern = (uu___111_8297.is_pattern);
        instantiate_imp = (uu___111_8297.instantiate_imp);
        effects = (uu___111_8297.effects);
        generalize = (uu___111_8297.generalize);
        letrecs = (uu___111_8297.letrecs);
        top_level = (uu___111_8297.top_level);
        check_uvars = (uu___111_8297.check_uvars);
        use_eq = (uu___111_8297.use_eq);
        is_iface = (uu___111_8297.is_iface);
        admit = (uu___111_8297.admit);
        lax = (uu___111_8297.lax);
        lax_universes = (uu___111_8297.lax_universes);
        failhard = (uu___111_8297.failhard);
        nosynth = (uu___111_8297.nosynth);
        uvar_subtyping = (uu___111_8297.uvar_subtyping);
        tc_term = (uu___111_8297.tc_term);
        type_of = (uu___111_8297.type_of);
        universe_of = (uu___111_8297.universe_of);
        check_type_of = (uu___111_8297.check_type_of);
        use_bv_sorts = (uu___111_8297.use_bv_sorts);
        qtbl_name_and_index = (uu___111_8297.qtbl_name_and_index);
        normalized_eff_names = (uu___111_8297.normalized_eff_names);
        proof_ns = (uu___111_8297.proof_ns);
        synth_hook = (uu___111_8297.synth_hook);
        splice = (uu___111_8297.splice);
        is_native_tactic = (uu___111_8297.is_native_tactic);
        identifier_info = (uu___111_8297.identifier_info);
        tc_hooks = (uu___111_8297.tc_hooks);
        dsenv = (uu___111_8297.dsenv);
        dep_graph = (uu___111_8297.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8305  -> fun uu____8306  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___112_8326 = env  in
      {
        solver = (uu___112_8326.solver);
        range = (uu___112_8326.range);
        curmodule = (uu___112_8326.curmodule);
        gamma = (uu___112_8326.gamma);
        gamma_sig = (uu___112_8326.gamma_sig);
        gamma_cache = (uu___112_8326.gamma_cache);
        modules = (uu___112_8326.modules);
        expected_typ = (uu___112_8326.expected_typ);
        sigtab = (uu___112_8326.sigtab);
        is_pattern = (uu___112_8326.is_pattern);
        instantiate_imp = (uu___112_8326.instantiate_imp);
        effects = (uu___112_8326.effects);
        generalize = (uu___112_8326.generalize);
        letrecs = (uu___112_8326.letrecs);
        top_level = (uu___112_8326.top_level);
        check_uvars = (uu___112_8326.check_uvars);
        use_eq = (uu___112_8326.use_eq);
        is_iface = (uu___112_8326.is_iface);
        admit = (uu___112_8326.admit);
        lax = (uu___112_8326.lax);
        lax_universes = (uu___112_8326.lax_universes);
        failhard = (uu___112_8326.failhard);
        nosynth = (uu___112_8326.nosynth);
        uvar_subtyping = (uu___112_8326.uvar_subtyping);
        tc_term = (uu___112_8326.tc_term);
        type_of = (uu___112_8326.type_of);
        universe_of = (uu___112_8326.universe_of);
        check_type_of = (uu___112_8326.check_type_of);
        use_bv_sorts = (uu___112_8326.use_bv_sorts);
        qtbl_name_and_index = (uu___112_8326.qtbl_name_and_index);
        normalized_eff_names = (uu___112_8326.normalized_eff_names);
        proof_ns = (uu___112_8326.proof_ns);
        synth_hook = (uu___112_8326.synth_hook);
        splice = (uu___112_8326.splice);
        is_native_tactic = (uu___112_8326.is_native_tactic);
        identifier_info = (uu___112_8326.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___112_8326.dsenv);
        dep_graph = (uu___112_8326.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___113_8337 = e  in
      {
        solver = (uu___113_8337.solver);
        range = (uu___113_8337.range);
        curmodule = (uu___113_8337.curmodule);
        gamma = (uu___113_8337.gamma);
        gamma_sig = (uu___113_8337.gamma_sig);
        gamma_cache = (uu___113_8337.gamma_cache);
        modules = (uu___113_8337.modules);
        expected_typ = (uu___113_8337.expected_typ);
        sigtab = (uu___113_8337.sigtab);
        is_pattern = (uu___113_8337.is_pattern);
        instantiate_imp = (uu___113_8337.instantiate_imp);
        effects = (uu___113_8337.effects);
        generalize = (uu___113_8337.generalize);
        letrecs = (uu___113_8337.letrecs);
        top_level = (uu___113_8337.top_level);
        check_uvars = (uu___113_8337.check_uvars);
        use_eq = (uu___113_8337.use_eq);
        is_iface = (uu___113_8337.is_iface);
        admit = (uu___113_8337.admit);
        lax = (uu___113_8337.lax);
        lax_universes = (uu___113_8337.lax_universes);
        failhard = (uu___113_8337.failhard);
        nosynth = (uu___113_8337.nosynth);
        uvar_subtyping = (uu___113_8337.uvar_subtyping);
        tc_term = (uu___113_8337.tc_term);
        type_of = (uu___113_8337.type_of);
        universe_of = (uu___113_8337.universe_of);
        check_type_of = (uu___113_8337.check_type_of);
        use_bv_sorts = (uu___113_8337.use_bv_sorts);
        qtbl_name_and_index = (uu___113_8337.qtbl_name_and_index);
        normalized_eff_names = (uu___113_8337.normalized_eff_names);
        proof_ns = (uu___113_8337.proof_ns);
        synth_hook = (uu___113_8337.synth_hook);
        splice = (uu___113_8337.splice);
        is_native_tactic = (uu___113_8337.is_native_tactic);
        identifier_info = (uu___113_8337.identifier_info);
        tc_hooks = (uu___113_8337.tc_hooks);
        dsenv = (uu___113_8337.dsenv);
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
      | (NoDelta ,uu____8360) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8361,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8362,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8363 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8372 . unit -> 'Auu____8372 FStar_Util.smap =
  fun uu____8379  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8384 . unit -> 'Auu____8384 FStar_Util.smap =
  fun uu____8391  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8501 = new_gamma_cache ()  in
                let uu____8504 = new_sigtab ()  in
                let uu____8507 =
                  let uu____8520 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8520, FStar_Pervasives_Native.None)  in
                let uu____8535 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8538 = FStar_Options.using_facts_from ()  in
                let uu____8539 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8542 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_sig = [];
                  gamma_cache = uu____8501;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8504;
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
                  uvar_subtyping = true;
                  tc_term;
                  type_of;
                  universe_of;
                  check_type_of;
                  use_bv_sorts = false;
                  qtbl_name_and_index = uu____8507;
                  normalized_eff_names = uu____8535;
                  proof_ns = uu____8538;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8578  -> false);
                  identifier_info = uu____8539;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8542;
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
  fun uu____8669  ->
    let uu____8670 = FStar_ST.op_Bang query_indices  in
    match uu____8670 with
    | [] -> failwith "Empty query indices!"
    | uu____8724 ->
        let uu____8733 =
          let uu____8742 =
            let uu____8749 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8749  in
          let uu____8803 = FStar_ST.op_Bang query_indices  in uu____8742 ::
            uu____8803
           in
        FStar_ST.op_Colon_Equals query_indices uu____8733
  
let (pop_query_indices : unit -> unit) =
  fun uu____8900  ->
    let uu____8901 = FStar_ST.op_Bang query_indices  in
    match uu____8901 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9024  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9054  ->
    match uu____9054 with
    | (l,n1) ->
        let uu____9061 = FStar_ST.op_Bang query_indices  in
        (match uu____9061 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9180 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9199  ->
    let uu____9200 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9200
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9277 =
       let uu____9280 = FStar_ST.op_Bang stack  in env :: uu____9280  in
     FStar_ST.op_Colon_Equals stack uu____9277);
    (let uu___114_9337 = env  in
     let uu____9338 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9341 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9344 =
       let uu____9357 =
         let uu____9360 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9360  in
       let uu____9385 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9357, uu____9385)  in
     let uu____9426 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9429 =
       let uu____9432 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9432  in
     {
       solver = (uu___114_9337.solver);
       range = (uu___114_9337.range);
       curmodule = (uu___114_9337.curmodule);
       gamma = (uu___114_9337.gamma);
       gamma_sig = (uu___114_9337.gamma_sig);
       gamma_cache = uu____9338;
       modules = (uu___114_9337.modules);
       expected_typ = (uu___114_9337.expected_typ);
       sigtab = uu____9341;
       is_pattern = (uu___114_9337.is_pattern);
       instantiate_imp = (uu___114_9337.instantiate_imp);
       effects = (uu___114_9337.effects);
       generalize = (uu___114_9337.generalize);
       letrecs = (uu___114_9337.letrecs);
       top_level = (uu___114_9337.top_level);
       check_uvars = (uu___114_9337.check_uvars);
       use_eq = (uu___114_9337.use_eq);
       is_iface = (uu___114_9337.is_iface);
       admit = (uu___114_9337.admit);
       lax = (uu___114_9337.lax);
       lax_universes = (uu___114_9337.lax_universes);
       failhard = (uu___114_9337.failhard);
       nosynth = (uu___114_9337.nosynth);
       uvar_subtyping = (uu___114_9337.uvar_subtyping);
       tc_term = (uu___114_9337.tc_term);
       type_of = (uu___114_9337.type_of);
       universe_of = (uu___114_9337.universe_of);
       check_type_of = (uu___114_9337.check_type_of);
       use_bv_sorts = (uu___114_9337.use_bv_sorts);
       qtbl_name_and_index = uu____9344;
       normalized_eff_names = uu____9426;
       proof_ns = (uu___114_9337.proof_ns);
       synth_hook = (uu___114_9337.synth_hook);
       splice = (uu___114_9337.splice);
       is_native_tactic = (uu___114_9337.is_native_tactic);
       identifier_info = uu____9429;
       tc_hooks = (uu___114_9337.tc_hooks);
       dsenv = (uu___114_9337.dsenv);
       dep_graph = (uu___114_9337.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9482  ->
    let uu____9483 = FStar_ST.op_Bang stack  in
    match uu____9483 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9545 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____9617  ->
           let uu____9618 = snapshot_stack env  in
           match uu____9618 with
           | (stack_depth,env1) ->
               let uu____9643 = snapshot_query_indices ()  in
               (match uu____9643 with
                | (query_indices_depth,()) ->
                    let uu____9667 = (env1.solver).snapshot msg  in
                    (match uu____9667 with
                     | (solver_depth,()) ->
                         let uu____9709 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9709 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___115_9755 = env1  in
                                 {
                                   solver = (uu___115_9755.solver);
                                   range = (uu___115_9755.range);
                                   curmodule = (uu___115_9755.curmodule);
                                   gamma = (uu___115_9755.gamma);
                                   gamma_sig = (uu___115_9755.gamma_sig);
                                   gamma_cache = (uu___115_9755.gamma_cache);
                                   modules = (uu___115_9755.modules);
                                   expected_typ =
                                     (uu___115_9755.expected_typ);
                                   sigtab = (uu___115_9755.sigtab);
                                   is_pattern = (uu___115_9755.is_pattern);
                                   instantiate_imp =
                                     (uu___115_9755.instantiate_imp);
                                   effects = (uu___115_9755.effects);
                                   generalize = (uu___115_9755.generalize);
                                   letrecs = (uu___115_9755.letrecs);
                                   top_level = (uu___115_9755.top_level);
                                   check_uvars = (uu___115_9755.check_uvars);
                                   use_eq = (uu___115_9755.use_eq);
                                   is_iface = (uu___115_9755.is_iface);
                                   admit = (uu___115_9755.admit);
                                   lax = (uu___115_9755.lax);
                                   lax_universes =
                                     (uu___115_9755.lax_universes);
                                   failhard = (uu___115_9755.failhard);
                                   nosynth = (uu___115_9755.nosynth);
                                   uvar_subtyping =
                                     (uu___115_9755.uvar_subtyping);
                                   tc_term = (uu___115_9755.tc_term);
                                   type_of = (uu___115_9755.type_of);
                                   universe_of = (uu___115_9755.universe_of);
                                   check_type_of =
                                     (uu___115_9755.check_type_of);
                                   use_bv_sorts =
                                     (uu___115_9755.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___115_9755.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___115_9755.normalized_eff_names);
                                   proof_ns = (uu___115_9755.proof_ns);
                                   synth_hook = (uu___115_9755.synth_hook);
                                   splice = (uu___115_9755.splice);
                                   is_native_tactic =
                                     (uu___115_9755.is_native_tactic);
                                   identifier_info =
                                     (uu___115_9755.identifier_info);
                                   tc_hooks = (uu___115_9755.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___115_9755.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9786  ->
             let uu____9787 =
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
             match uu____9787 with
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
                             ((let uu____9913 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9913
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9924 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9924
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9951,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9983 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10009  ->
                  match uu____10009 with
                  | (m,uu____10015) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9983 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___116_10023 = env  in
               {
                 solver = (uu___116_10023.solver);
                 range = (uu___116_10023.range);
                 curmodule = (uu___116_10023.curmodule);
                 gamma = (uu___116_10023.gamma);
                 gamma_sig = (uu___116_10023.gamma_sig);
                 gamma_cache = (uu___116_10023.gamma_cache);
                 modules = (uu___116_10023.modules);
                 expected_typ = (uu___116_10023.expected_typ);
                 sigtab = (uu___116_10023.sigtab);
                 is_pattern = (uu___116_10023.is_pattern);
                 instantiate_imp = (uu___116_10023.instantiate_imp);
                 effects = (uu___116_10023.effects);
                 generalize = (uu___116_10023.generalize);
                 letrecs = (uu___116_10023.letrecs);
                 top_level = (uu___116_10023.top_level);
                 check_uvars = (uu___116_10023.check_uvars);
                 use_eq = (uu___116_10023.use_eq);
                 is_iface = (uu___116_10023.is_iface);
                 admit = (uu___116_10023.admit);
                 lax = (uu___116_10023.lax);
                 lax_universes = (uu___116_10023.lax_universes);
                 failhard = (uu___116_10023.failhard);
                 nosynth = (uu___116_10023.nosynth);
                 uvar_subtyping = (uu___116_10023.uvar_subtyping);
                 tc_term = (uu___116_10023.tc_term);
                 type_of = (uu___116_10023.type_of);
                 universe_of = (uu___116_10023.universe_of);
                 check_type_of = (uu___116_10023.check_type_of);
                 use_bv_sorts = (uu___116_10023.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___116_10023.normalized_eff_names);
                 proof_ns = (uu___116_10023.proof_ns);
                 synth_hook = (uu___116_10023.synth_hook);
                 splice = (uu___116_10023.splice);
                 is_native_tactic = (uu___116_10023.is_native_tactic);
                 identifier_info = (uu___116_10023.identifier_info);
                 tc_hooks = (uu___116_10023.tc_hooks);
                 dsenv = (uu___116_10023.dsenv);
                 dep_graph = (uu___116_10023.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____10036,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___117_10045 = env  in
               {
                 solver = (uu___117_10045.solver);
                 range = (uu___117_10045.range);
                 curmodule = (uu___117_10045.curmodule);
                 gamma = (uu___117_10045.gamma);
                 gamma_sig = (uu___117_10045.gamma_sig);
                 gamma_cache = (uu___117_10045.gamma_cache);
                 modules = (uu___117_10045.modules);
                 expected_typ = (uu___117_10045.expected_typ);
                 sigtab = (uu___117_10045.sigtab);
                 is_pattern = (uu___117_10045.is_pattern);
                 instantiate_imp = (uu___117_10045.instantiate_imp);
                 effects = (uu___117_10045.effects);
                 generalize = (uu___117_10045.generalize);
                 letrecs = (uu___117_10045.letrecs);
                 top_level = (uu___117_10045.top_level);
                 check_uvars = (uu___117_10045.check_uvars);
                 use_eq = (uu___117_10045.use_eq);
                 is_iface = (uu___117_10045.is_iface);
                 admit = (uu___117_10045.admit);
                 lax = (uu___117_10045.lax);
                 lax_universes = (uu___117_10045.lax_universes);
                 failhard = (uu___117_10045.failhard);
                 nosynth = (uu___117_10045.nosynth);
                 uvar_subtyping = (uu___117_10045.uvar_subtyping);
                 tc_term = (uu___117_10045.tc_term);
                 type_of = (uu___117_10045.type_of);
                 universe_of = (uu___117_10045.universe_of);
                 check_type_of = (uu___117_10045.check_type_of);
                 use_bv_sorts = (uu___117_10045.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___117_10045.normalized_eff_names);
                 proof_ns = (uu___117_10045.proof_ns);
                 synth_hook = (uu___117_10045.synth_hook);
                 splice = (uu___117_10045.splice);
                 is_native_tactic = (uu___117_10045.is_native_tactic);
                 identifier_info = (uu___117_10045.identifier_info);
                 tc_hooks = (uu___117_10045.tc_hooks);
                 dsenv = (uu___117_10045.dsenv);
                 dep_graph = (uu___117_10045.dep_graph)
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
        (let uu___118_10079 = e  in
         {
           solver = (uu___118_10079.solver);
           range = r;
           curmodule = (uu___118_10079.curmodule);
           gamma = (uu___118_10079.gamma);
           gamma_sig = (uu___118_10079.gamma_sig);
           gamma_cache = (uu___118_10079.gamma_cache);
           modules = (uu___118_10079.modules);
           expected_typ = (uu___118_10079.expected_typ);
           sigtab = (uu___118_10079.sigtab);
           is_pattern = (uu___118_10079.is_pattern);
           instantiate_imp = (uu___118_10079.instantiate_imp);
           effects = (uu___118_10079.effects);
           generalize = (uu___118_10079.generalize);
           letrecs = (uu___118_10079.letrecs);
           top_level = (uu___118_10079.top_level);
           check_uvars = (uu___118_10079.check_uvars);
           use_eq = (uu___118_10079.use_eq);
           is_iface = (uu___118_10079.is_iface);
           admit = (uu___118_10079.admit);
           lax = (uu___118_10079.lax);
           lax_universes = (uu___118_10079.lax_universes);
           failhard = (uu___118_10079.failhard);
           nosynth = (uu___118_10079.nosynth);
           uvar_subtyping = (uu___118_10079.uvar_subtyping);
           tc_term = (uu___118_10079.tc_term);
           type_of = (uu___118_10079.type_of);
           universe_of = (uu___118_10079.universe_of);
           check_type_of = (uu___118_10079.check_type_of);
           use_bv_sorts = (uu___118_10079.use_bv_sorts);
           qtbl_name_and_index = (uu___118_10079.qtbl_name_and_index);
           normalized_eff_names = (uu___118_10079.normalized_eff_names);
           proof_ns = (uu___118_10079.proof_ns);
           synth_hook = (uu___118_10079.synth_hook);
           splice = (uu___118_10079.splice);
           is_native_tactic = (uu___118_10079.is_native_tactic);
           identifier_info = (uu___118_10079.identifier_info);
           tc_hooks = (uu___118_10079.tc_hooks);
           dsenv = (uu___118_10079.dsenv);
           dep_graph = (uu___118_10079.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10095 =
        let uu____10096 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10096 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10095
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10158 =
          let uu____10159 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10159 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10158
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10221 =
          let uu____10222 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10222 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10221
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10284 =
        let uu____10285 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10285 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10284
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___119_10354 = env  in
      {
        solver = (uu___119_10354.solver);
        range = (uu___119_10354.range);
        curmodule = lid;
        gamma = (uu___119_10354.gamma);
        gamma_sig = (uu___119_10354.gamma_sig);
        gamma_cache = (uu___119_10354.gamma_cache);
        modules = (uu___119_10354.modules);
        expected_typ = (uu___119_10354.expected_typ);
        sigtab = (uu___119_10354.sigtab);
        is_pattern = (uu___119_10354.is_pattern);
        instantiate_imp = (uu___119_10354.instantiate_imp);
        effects = (uu___119_10354.effects);
        generalize = (uu___119_10354.generalize);
        letrecs = (uu___119_10354.letrecs);
        top_level = (uu___119_10354.top_level);
        check_uvars = (uu___119_10354.check_uvars);
        use_eq = (uu___119_10354.use_eq);
        is_iface = (uu___119_10354.is_iface);
        admit = (uu___119_10354.admit);
        lax = (uu___119_10354.lax);
        lax_universes = (uu___119_10354.lax_universes);
        failhard = (uu___119_10354.failhard);
        nosynth = (uu___119_10354.nosynth);
        uvar_subtyping = (uu___119_10354.uvar_subtyping);
        tc_term = (uu___119_10354.tc_term);
        type_of = (uu___119_10354.type_of);
        universe_of = (uu___119_10354.universe_of);
        check_type_of = (uu___119_10354.check_type_of);
        use_bv_sorts = (uu___119_10354.use_bv_sorts);
        qtbl_name_and_index = (uu___119_10354.qtbl_name_and_index);
        normalized_eff_names = (uu___119_10354.normalized_eff_names);
        proof_ns = (uu___119_10354.proof_ns);
        synth_hook = (uu___119_10354.synth_hook);
        splice = (uu___119_10354.splice);
        is_native_tactic = (uu___119_10354.is_native_tactic);
        identifier_info = (uu___119_10354.identifier_info);
        tc_hooks = (uu___119_10354.tc_hooks);
        dsenv = (uu___119_10354.dsenv);
        dep_graph = (uu___119_10354.dep_graph)
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
      let uu____10381 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10381
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10391 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10391)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10401 =
      let uu____10402 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10402  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10401)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10407  ->
    let uu____10408 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10408
  
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
      | ((formals,t),uu____10464) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10498 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10498)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___97_10514  ->
    match uu___97_10514 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10540  -> new_u_univ ()))
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
      let uu____10559 = inst_tscheme t  in
      match uu____10559 with
      | (us,t1) ->
          let uu____10570 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10570)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10590  ->
          match uu____10590 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10609 =
                         let uu____10610 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10611 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10612 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10613 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10610 uu____10611 uu____10612 uu____10613
                          in
                       failwith uu____10609)
                    else ();
                    (let uu____10615 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10615))
               | uu____10624 ->
                   let uu____10625 =
                     let uu____10626 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10626
                      in
                   failwith uu____10625)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10632 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10638 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10644 -> false
  
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
             | ([],uu____10686) -> Maybe
             | (uu____10693,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10712 -> No  in
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
          let uu____10803 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10803 with
          | FStar_Pervasives_Native.None  ->
              let uu____10826 =
                FStar_Util.find_map env.gamma
                  (fun uu___98_10870  ->
                     match uu___98_10870 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____10909 = FStar_Ident.lid_equals lid l  in
                         if uu____10909
                         then
                           let uu____10930 =
                             let uu____10949 =
                               let uu____10964 = inst_tscheme t  in
                               FStar_Util.Inl uu____10964  in
                             let uu____10979 = FStar_Ident.range_of_lid l  in
                             (uu____10949, uu____10979)  in
                           FStar_Pervasives_Native.Some uu____10930
                         else FStar_Pervasives_Native.None
                     | uu____11031 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____10826
                (fun uu____11069  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___99_11078  ->
                        match uu___99_11078 with
                        | (uu____11081,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11083);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11084;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11085;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11086;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11087;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11107 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11107
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
                                  uu____11155 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11162 -> cache t  in
                            let uu____11163 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11163 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11169 =
                                   let uu____11170 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11170)
                                    in
                                 maybe_cache uu____11169)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11238 = find_in_sigtab env lid  in
         match uu____11238 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11325) ->
          add_sigelts env ses
      | uu____11334 ->
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
            | uu____11348 -> ()))

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
        (fun uu___100_11379  ->
           match uu___100_11379 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11397 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11458,lb::[]),uu____11460) ->
            let uu____11467 =
              let uu____11476 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11485 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11476, uu____11485)  in
            FStar_Pervasives_Native.Some uu____11467
        | FStar_Syntax_Syntax.Sig_let ((uu____11498,lbs),uu____11500) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11530 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11542 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11542
                     then
                       let uu____11553 =
                         let uu____11562 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11571 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11562, uu____11571)  in
                       FStar_Pervasives_Native.Some uu____11553
                     else FStar_Pervasives_Native.None)
        | uu____11593 -> FStar_Pervasives_Native.None
  
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
          let uu____11652 =
            let uu____11661 =
              let uu____11666 =
                let uu____11667 =
                  let uu____11670 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11670
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11667)  in
              inst_tscheme1 uu____11666  in
            (uu____11661, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11652
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11692,uu____11693) ->
          let uu____11698 =
            let uu____11707 =
              let uu____11712 =
                let uu____11713 =
                  let uu____11716 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11716  in
                (us, uu____11713)  in
              inst_tscheme1 uu____11712  in
            (uu____11707, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11698
      | uu____11735 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11823 =
          match uu____11823 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11919,uvs,t,uu____11922,uu____11923,uu____11924);
                      FStar_Syntax_Syntax.sigrng = uu____11925;
                      FStar_Syntax_Syntax.sigquals = uu____11926;
                      FStar_Syntax_Syntax.sigmeta = uu____11927;
                      FStar_Syntax_Syntax.sigattrs = uu____11928;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11949 =
                     let uu____11958 = inst_tscheme1 (uvs, t)  in
                     (uu____11958, rng)  in
                   FStar_Pervasives_Native.Some uu____11949
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11982;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11984;
                      FStar_Syntax_Syntax.sigattrs = uu____11985;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12002 =
                     let uu____12003 = in_cur_mod env l  in uu____12003 = Yes
                      in
                   if uu____12002
                   then
                     let uu____12014 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12014
                      then
                        let uu____12027 =
                          let uu____12036 = inst_tscheme1 (uvs, t)  in
                          (uu____12036, rng)  in
                        FStar_Pervasives_Native.Some uu____12027
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12067 =
                        let uu____12076 = inst_tscheme1 (uvs, t)  in
                        (uu____12076, rng)  in
                      FStar_Pervasives_Native.Some uu____12067)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12101,uu____12102);
                      FStar_Syntax_Syntax.sigrng = uu____12103;
                      FStar_Syntax_Syntax.sigquals = uu____12104;
                      FStar_Syntax_Syntax.sigmeta = uu____12105;
                      FStar_Syntax_Syntax.sigattrs = uu____12106;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12145 =
                          let uu____12154 = inst_tscheme1 (uvs, k)  in
                          (uu____12154, rng)  in
                        FStar_Pervasives_Native.Some uu____12145
                    | uu____12175 ->
                        let uu____12176 =
                          let uu____12185 =
                            let uu____12190 =
                              let uu____12191 =
                                let uu____12194 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12194
                                 in
                              (uvs, uu____12191)  in
                            inst_tscheme1 uu____12190  in
                          (uu____12185, rng)  in
                        FStar_Pervasives_Native.Some uu____12176)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12217,uu____12218);
                      FStar_Syntax_Syntax.sigrng = uu____12219;
                      FStar_Syntax_Syntax.sigquals = uu____12220;
                      FStar_Syntax_Syntax.sigmeta = uu____12221;
                      FStar_Syntax_Syntax.sigattrs = uu____12222;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12262 =
                          let uu____12271 = inst_tscheme_with (uvs, k) us  in
                          (uu____12271, rng)  in
                        FStar_Pervasives_Native.Some uu____12262
                    | uu____12292 ->
                        let uu____12293 =
                          let uu____12302 =
                            let uu____12307 =
                              let uu____12308 =
                                let uu____12311 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12311
                                 in
                              (uvs, uu____12308)  in
                            inst_tscheme_with uu____12307 us  in
                          (uu____12302, rng)  in
                        FStar_Pervasives_Native.Some uu____12293)
               | FStar_Util.Inr se ->
                   let uu____12347 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12368;
                          FStar_Syntax_Syntax.sigrng = uu____12369;
                          FStar_Syntax_Syntax.sigquals = uu____12370;
                          FStar_Syntax_Syntax.sigmeta = uu____12371;
                          FStar_Syntax_Syntax.sigattrs = uu____12372;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12387 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12347
                     (FStar_Util.map_option
                        (fun uu____12435  ->
                           match uu____12435 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12466 =
          let uu____12477 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12477 mapper  in
        match uu____12466 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12551 =
              let uu____12562 =
                let uu____12569 =
                  let uu___120_12572 = t  in
                  let uu____12573 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___120_12572.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12573;
                    FStar_Syntax_Syntax.vars =
                      (uu___120_12572.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12569)  in
              (uu____12562, r)  in
            FStar_Pervasives_Native.Some uu____12551
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12620 = lookup_qname env l  in
      match uu____12620 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12639 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12691 = try_lookup_bv env bv  in
      match uu____12691 with
      | FStar_Pervasives_Native.None  ->
          let uu____12706 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12706 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12721 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12722 =
            let uu____12723 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12723  in
          (uu____12721, uu____12722)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12744 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12744 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12810 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12810  in
          let uu____12811 =
            let uu____12820 =
              let uu____12825 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12825)  in
            (uu____12820, r1)  in
          FStar_Pervasives_Native.Some uu____12811
  
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
        let uu____12859 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12859 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12892,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12917 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12917  in
            let uu____12918 =
              let uu____12923 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12923, r1)  in
            FStar_Pervasives_Native.Some uu____12918
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12946 = try_lookup_lid env l  in
      match uu____12946 with
      | FStar_Pervasives_Native.None  ->
          let uu____12973 = name_not_found l  in
          let uu____12978 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12973 uu____12978
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_13018  ->
              match uu___101_13018 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13020 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13039 = lookup_qname env lid  in
      match uu____13039 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13048,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13051;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13053;
              FStar_Syntax_Syntax.sigattrs = uu____13054;_},FStar_Pervasives_Native.None
            ),uu____13055)
          ->
          let uu____13104 =
            let uu____13111 =
              let uu____13112 =
                let uu____13115 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13115 t  in
              (uvs, uu____13112)  in
            (uu____13111, q)  in
          FStar_Pervasives_Native.Some uu____13104
      | uu____13128 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13149 = lookup_qname env lid  in
      match uu____13149 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13154,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13157;
              FStar_Syntax_Syntax.sigquals = uu____13158;
              FStar_Syntax_Syntax.sigmeta = uu____13159;
              FStar_Syntax_Syntax.sigattrs = uu____13160;_},FStar_Pervasives_Native.None
            ),uu____13161)
          ->
          let uu____13210 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13210 (uvs, t)
      | uu____13215 ->
          let uu____13216 = name_not_found lid  in
          let uu____13221 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13216 uu____13221
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13240 = lookup_qname env lid  in
      match uu____13240 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13245,uvs,t,uu____13248,uu____13249,uu____13250);
              FStar_Syntax_Syntax.sigrng = uu____13251;
              FStar_Syntax_Syntax.sigquals = uu____13252;
              FStar_Syntax_Syntax.sigmeta = uu____13253;
              FStar_Syntax_Syntax.sigattrs = uu____13254;_},FStar_Pervasives_Native.None
            ),uu____13255)
          ->
          let uu____13308 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13308 (uvs, t)
      | uu____13313 ->
          let uu____13314 = name_not_found lid  in
          let uu____13319 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13314 uu____13319
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13340 = lookup_qname env lid  in
      match uu____13340 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13347,uu____13348,uu____13349,uu____13350,uu____13351,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13353;
              FStar_Syntax_Syntax.sigquals = uu____13354;
              FStar_Syntax_Syntax.sigmeta = uu____13355;
              FStar_Syntax_Syntax.sigattrs = uu____13356;_},uu____13357),uu____13358)
          -> (true, dcs)
      | uu____13419 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13432 = lookup_qname env lid  in
      match uu____13432 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13433,uu____13434,uu____13435,l,uu____13437,uu____13438);
              FStar_Syntax_Syntax.sigrng = uu____13439;
              FStar_Syntax_Syntax.sigquals = uu____13440;
              FStar_Syntax_Syntax.sigmeta = uu____13441;
              FStar_Syntax_Syntax.sigattrs = uu____13442;_},uu____13443),uu____13444)
          -> l
      | uu____13499 ->
          let uu____13500 =
            let uu____13501 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13501  in
          failwith uu____13500
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13550)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13601,lbs),uu____13603)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13625 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13625
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13657 -> FStar_Pervasives_Native.None)
        | uu____13662 -> FStar_Pervasives_Native.None
  
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
        let uu____13692 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13692
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13717),uu____13718) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13767 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13788 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13788
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13807 = lookup_qname env ftv  in
      match uu____13807 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13811) ->
          let uu____13856 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13856 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13877,t),r) ->
               let uu____13892 =
                 let uu____13893 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13893 t  in
               FStar_Pervasives_Native.Some uu____13892)
      | uu____13894 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13905 = try_lookup_effect_lid env ftv  in
      match uu____13905 with
      | FStar_Pervasives_Native.None  ->
          let uu____13908 = name_not_found ftv  in
          let uu____13913 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13908 uu____13913
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
        let uu____13936 = lookup_qname env lid0  in
        match uu____13936 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13947);
                FStar_Syntax_Syntax.sigrng = uu____13948;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13950;
                FStar_Syntax_Syntax.sigattrs = uu____13951;_},FStar_Pervasives_Native.None
              ),uu____13952)
            ->
            let lid1 =
              let uu____14006 =
                let uu____14007 = FStar_Ident.range_of_lid lid  in
                let uu____14008 =
                  let uu____14009 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14009  in
                FStar_Range.set_use_range uu____14007 uu____14008  in
              FStar_Ident.set_lid_range lid uu____14006  in
            let uu____14010 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_14014  ->
                      match uu___102_14014 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14015 -> false))
               in
            if uu____14010
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14029 =
                      let uu____14030 =
                        let uu____14031 = get_range env  in
                        FStar_Range.string_of_range uu____14031  in
                      let uu____14032 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14033 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14030 uu____14032 uu____14033
                       in
                    failwith uu____14029)
                  in
               match (binders, univs1) with
               | ([],uu____14048) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14069,uu____14070::uu____14071::uu____14072) ->
                   let uu____14089 =
                     let uu____14090 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14091 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14090 uu____14091
                      in
                   failwith uu____14089
               | uu____14098 ->
                   let uu____14111 =
                     let uu____14116 =
                       let uu____14117 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14117)  in
                     inst_tscheme_with uu____14116 insts  in
                   (match uu____14111 with
                    | (uu____14130,t) ->
                        let t1 =
                          let uu____14133 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14133 t  in
                        let uu____14134 =
                          let uu____14135 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14135.FStar_Syntax_Syntax.n  in
                        (match uu____14134 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14166 -> failwith "Impossible")))
        | uu____14173 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14196 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14196 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14209,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14216 = find1 l2  in
            (match uu____14216 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14223 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14223 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14227 = find1 l  in
            (match uu____14227 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14232 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14232
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14246 = lookup_qname env l1  in
      match uu____14246 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14249;
              FStar_Syntax_Syntax.sigrng = uu____14250;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14252;
              FStar_Syntax_Syntax.sigattrs = uu____14253;_},uu____14254),uu____14255)
          -> q
      | uu____14306 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14327 =
          let uu____14328 =
            let uu____14329 = FStar_Util.string_of_int i  in
            let uu____14330 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14329 uu____14330
             in
          failwith uu____14328  in
        let uu____14331 = lookup_datacon env lid  in
        match uu____14331 with
        | (uu____14336,t) ->
            let uu____14338 =
              let uu____14339 = FStar_Syntax_Subst.compress t  in
              uu____14339.FStar_Syntax_Syntax.n  in
            (match uu____14338 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14343) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14374 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14374
                      FStar_Pervasives_Native.fst)
             | uu____14383 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14394 = lookup_qname env l  in
      match uu____14394 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14395,uu____14396,uu____14397);
              FStar_Syntax_Syntax.sigrng = uu____14398;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14400;
              FStar_Syntax_Syntax.sigattrs = uu____14401;_},uu____14402),uu____14403)
          ->
          FStar_Util.for_some
            (fun uu___103_14456  ->
               match uu___103_14456 with
               | FStar_Syntax_Syntax.Projector uu____14457 -> true
               | uu____14462 -> false) quals
      | uu____14463 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14474 = lookup_qname env lid  in
      match uu____14474 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14475,uu____14476,uu____14477,uu____14478,uu____14479,uu____14480);
              FStar_Syntax_Syntax.sigrng = uu____14481;
              FStar_Syntax_Syntax.sigquals = uu____14482;
              FStar_Syntax_Syntax.sigmeta = uu____14483;
              FStar_Syntax_Syntax.sigattrs = uu____14484;_},uu____14485),uu____14486)
          -> true
      | uu____14541 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14552 = lookup_qname env lid  in
      match uu____14552 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14553,uu____14554,uu____14555,uu____14556,uu____14557,uu____14558);
              FStar_Syntax_Syntax.sigrng = uu____14559;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14561;
              FStar_Syntax_Syntax.sigattrs = uu____14562;_},uu____14563),uu____14564)
          ->
          FStar_Util.for_some
            (fun uu___104_14625  ->
               match uu___104_14625 with
               | FStar_Syntax_Syntax.RecordType uu____14626 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14635 -> true
               | uu____14644 -> false) quals
      | uu____14645 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14651,uu____14652);
            FStar_Syntax_Syntax.sigrng = uu____14653;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14655;
            FStar_Syntax_Syntax.sigattrs = uu____14656;_},uu____14657),uu____14658)
        ->
        FStar_Util.for_some
          (fun uu___105_14715  ->
             match uu___105_14715 with
             | FStar_Syntax_Syntax.Action uu____14716 -> true
             | uu____14717 -> false) quals
    | uu____14718 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14729 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14729
  
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
      let uu____14743 =
        let uu____14744 = FStar_Syntax_Util.un_uinst head1  in
        uu____14744.FStar_Syntax_Syntax.n  in
      match uu____14743 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14748 ->
               true
           | uu____14749 -> false)
      | uu____14750 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14761 = lookup_qname env l  in
      match uu____14761 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14763),uu____14764) ->
          FStar_Util.for_some
            (fun uu___106_14812  ->
               match uu___106_14812 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14813 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14814 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14885 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14901) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14918 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14925 ->
                 FStar_Pervasives_Native.Some true
             | uu____14942 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14943 =
        let uu____14946 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14946 mapper  in
      match uu____14943 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14996 = lookup_qname env lid  in
      match uu____14996 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14997,uu____14998,tps,uu____15000,uu____15001,uu____15002);
              FStar_Syntax_Syntax.sigrng = uu____15003;
              FStar_Syntax_Syntax.sigquals = uu____15004;
              FStar_Syntax_Syntax.sigmeta = uu____15005;
              FStar_Syntax_Syntax.sigattrs = uu____15006;_},uu____15007),uu____15008)
          -> FStar_List.length tps
      | uu____15071 ->
          let uu____15072 = name_not_found lid  in
          let uu____15077 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15072 uu____15077
  
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
           (fun uu____15121  ->
              match uu____15121 with
              | (d,uu____15129) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15144 = effect_decl_opt env l  in
      match uu____15144 with
      | FStar_Pervasives_Native.None  ->
          let uu____15159 = name_not_found l  in
          let uu____15164 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15159 uu____15164
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15186  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15205  ->
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
        let uu____15236 = FStar_Ident.lid_equals l1 l2  in
        if uu____15236
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15244 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15244
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15252 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15305  ->
                        match uu____15305 with
                        | (m1,m2,uu____15318,uu____15319,uu____15320) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15252 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15337 =
                    let uu____15342 =
                      let uu____15343 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15344 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15343
                        uu____15344
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15342)
                     in
                  FStar_Errors.raise_error uu____15337 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15351,uu____15352,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15385 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15385
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
  'Auu____15401 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15401)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15430 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15456  ->
                match uu____15456 with
                | (d,uu____15462) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15430 with
      | FStar_Pervasives_Native.None  ->
          let uu____15473 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15473
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15486 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15486 with
           | (uu____15501,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15517)::(wp,uu____15519)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15555 -> failwith "Impossible"))
  
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
          let uu____15608 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15608
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15610 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15610
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
                  let uu____15618 = get_range env  in
                  let uu____15619 =
                    let uu____15626 =
                      let uu____15627 =
                        let uu____15642 =
                          let uu____15651 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15651]  in
                        (null_wp, uu____15642)  in
                      FStar_Syntax_Syntax.Tm_app uu____15627  in
                    FStar_Syntax_Syntax.mk uu____15626  in
                  uu____15619 FStar_Pervasives_Native.None uu____15618  in
                let uu____15683 =
                  let uu____15684 =
                    let uu____15693 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15693]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15684;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15683))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_15724 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_15724.order);
              joins = (uu___121_15724.joins)
            }  in
          let uu___122_15733 = env  in
          {
            solver = (uu___122_15733.solver);
            range = (uu___122_15733.range);
            curmodule = (uu___122_15733.curmodule);
            gamma = (uu___122_15733.gamma);
            gamma_sig = (uu___122_15733.gamma_sig);
            gamma_cache = (uu___122_15733.gamma_cache);
            modules = (uu___122_15733.modules);
            expected_typ = (uu___122_15733.expected_typ);
            sigtab = (uu___122_15733.sigtab);
            is_pattern = (uu___122_15733.is_pattern);
            instantiate_imp = (uu___122_15733.instantiate_imp);
            effects;
            generalize = (uu___122_15733.generalize);
            letrecs = (uu___122_15733.letrecs);
            top_level = (uu___122_15733.top_level);
            check_uvars = (uu___122_15733.check_uvars);
            use_eq = (uu___122_15733.use_eq);
            is_iface = (uu___122_15733.is_iface);
            admit = (uu___122_15733.admit);
            lax = (uu___122_15733.lax);
            lax_universes = (uu___122_15733.lax_universes);
            failhard = (uu___122_15733.failhard);
            nosynth = (uu___122_15733.nosynth);
            uvar_subtyping = (uu___122_15733.uvar_subtyping);
            tc_term = (uu___122_15733.tc_term);
            type_of = (uu___122_15733.type_of);
            universe_of = (uu___122_15733.universe_of);
            check_type_of = (uu___122_15733.check_type_of);
            use_bv_sorts = (uu___122_15733.use_bv_sorts);
            qtbl_name_and_index = (uu___122_15733.qtbl_name_and_index);
            normalized_eff_names = (uu___122_15733.normalized_eff_names);
            proof_ns = (uu___122_15733.proof_ns);
            synth_hook = (uu___122_15733.synth_hook);
            splice = (uu___122_15733.splice);
            is_native_tactic = (uu___122_15733.is_native_tactic);
            identifier_info = (uu___122_15733.identifier_info);
            tc_hooks = (uu___122_15733.tc_hooks);
            dsenv = (uu___122_15733.dsenv);
            dep_graph = (uu___122_15733.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15763 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15763  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15921 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15922 = l1 u t wp e  in
                                l2 u t uu____15921 uu____15922))
                | uu____15923 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15995 = inst_tscheme_with lift_t [u]  in
            match uu____15995 with
            | (uu____16002,lift_t1) ->
                let uu____16004 =
                  let uu____16011 =
                    let uu____16012 =
                      let uu____16027 =
                        let uu____16036 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16043 =
                          let uu____16052 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16052]  in
                        uu____16036 :: uu____16043  in
                      (lift_t1, uu____16027)  in
                    FStar_Syntax_Syntax.Tm_app uu____16012  in
                  FStar_Syntax_Syntax.mk uu____16011  in
                uu____16004 FStar_Pervasives_Native.None
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
            let uu____16154 = inst_tscheme_with lift_t [u]  in
            match uu____16154 with
            | (uu____16161,lift_t1) ->
                let uu____16163 =
                  let uu____16170 =
                    let uu____16171 =
                      let uu____16186 =
                        let uu____16195 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16202 =
                          let uu____16211 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16218 =
                            let uu____16227 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16227]  in
                          uu____16211 :: uu____16218  in
                        uu____16195 :: uu____16202  in
                      (lift_t1, uu____16186)  in
                    FStar_Syntax_Syntax.Tm_app uu____16171  in
                  FStar_Syntax_Syntax.mk uu____16170  in
                uu____16163 FStar_Pervasives_Native.None
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
              let uu____16317 =
                let uu____16318 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16318
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16317  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16322 =
              let uu____16323 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16323  in
            let uu____16324 =
              let uu____16325 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16351 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16351)
                 in
              FStar_Util.dflt "none" uu____16325  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16322
              uu____16324
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16377  ->
                    match uu____16377 with
                    | (e,uu____16385) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16408 =
            match uu____16408 with
            | (i,j) ->
                let uu____16419 = FStar_Ident.lid_equals i j  in
                if uu____16419
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
              let uu____16451 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16461 = FStar_Ident.lid_equals i k  in
                        if uu____16461
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16472 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16472
                                  then []
                                  else
                                    (let uu____16476 =
                                       let uu____16485 =
                                         find_edge order1 (i, k)  in
                                       let uu____16488 =
                                         find_edge order1 (k, j)  in
                                       (uu____16485, uu____16488)  in
                                     match uu____16476 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16503 =
                                           compose_edges e1 e2  in
                                         [uu____16503]
                                     | uu____16504 -> [])))))
                 in
              FStar_List.append order1 uu____16451  in
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
                   let uu____16534 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16536 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16536
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16534
                   then
                     let uu____16541 =
                       let uu____16546 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16546)
                        in
                     let uu____16547 = get_range env  in
                     FStar_Errors.raise_error uu____16541 uu____16547
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16624 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16624
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16673 =
                                              let uu____16682 =
                                                find_edge order2 (i, k)  in
                                              let uu____16685 =
                                                find_edge order2 (j, k)  in
                                              (uu____16682, uu____16685)  in
                                            match uu____16673 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16727,uu____16728)
                                                     ->
                                                     let uu____16735 =
                                                       let uu____16740 =
                                                         let uu____16741 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16741
                                                          in
                                                       let uu____16744 =
                                                         let uu____16745 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16745
                                                          in
                                                       (uu____16740,
                                                         uu____16744)
                                                        in
                                                     (match uu____16735 with
                                                      | (true ,true ) ->
                                                          let uu____16756 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16756
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
                                            | uu____16781 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___123_16854 = env.effects  in
              { decls = (uu___123_16854.decls); order = order2; joins }  in
            let uu___124_16855 = env  in
            {
              solver = (uu___124_16855.solver);
              range = (uu___124_16855.range);
              curmodule = (uu___124_16855.curmodule);
              gamma = (uu___124_16855.gamma);
              gamma_sig = (uu___124_16855.gamma_sig);
              gamma_cache = (uu___124_16855.gamma_cache);
              modules = (uu___124_16855.modules);
              expected_typ = (uu___124_16855.expected_typ);
              sigtab = (uu___124_16855.sigtab);
              is_pattern = (uu___124_16855.is_pattern);
              instantiate_imp = (uu___124_16855.instantiate_imp);
              effects;
              generalize = (uu___124_16855.generalize);
              letrecs = (uu___124_16855.letrecs);
              top_level = (uu___124_16855.top_level);
              check_uvars = (uu___124_16855.check_uvars);
              use_eq = (uu___124_16855.use_eq);
              is_iface = (uu___124_16855.is_iface);
              admit = (uu___124_16855.admit);
              lax = (uu___124_16855.lax);
              lax_universes = (uu___124_16855.lax_universes);
              failhard = (uu___124_16855.failhard);
              nosynth = (uu___124_16855.nosynth);
              uvar_subtyping = (uu___124_16855.uvar_subtyping);
              tc_term = (uu___124_16855.tc_term);
              type_of = (uu___124_16855.type_of);
              universe_of = (uu___124_16855.universe_of);
              check_type_of = (uu___124_16855.check_type_of);
              use_bv_sorts = (uu___124_16855.use_bv_sorts);
              qtbl_name_and_index = (uu___124_16855.qtbl_name_and_index);
              normalized_eff_names = (uu___124_16855.normalized_eff_names);
              proof_ns = (uu___124_16855.proof_ns);
              synth_hook = (uu___124_16855.synth_hook);
              splice = (uu___124_16855.splice);
              is_native_tactic = (uu___124_16855.is_native_tactic);
              identifier_info = (uu___124_16855.identifier_info);
              tc_hooks = (uu___124_16855.tc_hooks);
              dsenv = (uu___124_16855.dsenv);
              dep_graph = (uu___124_16855.dep_graph)
            }))
      | uu____16856 -> env
  
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
        | uu____16884 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16896 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16896 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16913 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16913 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16931 =
                     let uu____16936 =
                       let uu____16937 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16942 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16949 =
                         let uu____16950 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16950  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16937 uu____16942 uu____16949
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16936)
                      in
                   FStar_Errors.raise_error uu____16931
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16955 =
                     let uu____16964 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16964 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16993  ->
                        fun uu____16994  ->
                          match (uu____16993, uu____16994) with
                          | ((x,uu____17016),(t,uu____17018)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16955
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____17037 =
                     let uu___125_17038 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_17038.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_17038.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_17038.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_17038.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____17037
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
          let uu____17068 = effect_decl_opt env effect_name  in
          match uu____17068 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17101 =
                only_reifiable &&
                  (let uu____17103 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17103)
                 in
              if uu____17101
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17119 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____17138 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____17167 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____17167
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____17168 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____17168
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____17180 =
                       let uu____17183 = get_range env  in
                       let uu____17184 =
                         let uu____17191 =
                           let uu____17192 =
                             let uu____17207 =
                               let uu____17216 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17216; wp]  in
                             (repr, uu____17207)  in
                           FStar_Syntax_Syntax.Tm_app uu____17192  in
                         FStar_Syntax_Syntax.mk uu____17191  in
                       uu____17184 FStar_Pervasives_Native.None uu____17183
                        in
                     FStar_Pervasives_Native.Some uu____17180)
  
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
          let uu____17296 =
            let uu____17301 =
              let uu____17302 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17302
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17301)  in
          let uu____17303 = get_range env  in
          FStar_Errors.raise_error uu____17296 uu____17303  in
        let uu____17304 = effect_repr_aux true env c u_c  in
        match uu____17304 with
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
      | uu____17350 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17361 =
        let uu____17362 = FStar_Syntax_Subst.compress t  in
        uu____17362.FStar_Syntax_Syntax.n  in
      match uu____17361 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17365,c) ->
          is_reifiable_comp env c
      | uu____17383 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___126_17404 = env  in
        {
          solver = (uu___126_17404.solver);
          range = (uu___126_17404.range);
          curmodule = (uu___126_17404.curmodule);
          gamma = (uu___126_17404.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___126_17404.gamma_cache);
          modules = (uu___126_17404.modules);
          expected_typ = (uu___126_17404.expected_typ);
          sigtab = (uu___126_17404.sigtab);
          is_pattern = (uu___126_17404.is_pattern);
          instantiate_imp = (uu___126_17404.instantiate_imp);
          effects = (uu___126_17404.effects);
          generalize = (uu___126_17404.generalize);
          letrecs = (uu___126_17404.letrecs);
          top_level = (uu___126_17404.top_level);
          check_uvars = (uu___126_17404.check_uvars);
          use_eq = (uu___126_17404.use_eq);
          is_iface = (uu___126_17404.is_iface);
          admit = (uu___126_17404.admit);
          lax = (uu___126_17404.lax);
          lax_universes = (uu___126_17404.lax_universes);
          failhard = (uu___126_17404.failhard);
          nosynth = (uu___126_17404.nosynth);
          uvar_subtyping = (uu___126_17404.uvar_subtyping);
          tc_term = (uu___126_17404.tc_term);
          type_of = (uu___126_17404.type_of);
          universe_of = (uu___126_17404.universe_of);
          check_type_of = (uu___126_17404.check_type_of);
          use_bv_sorts = (uu___126_17404.use_bv_sorts);
          qtbl_name_and_index = (uu___126_17404.qtbl_name_and_index);
          normalized_eff_names = (uu___126_17404.normalized_eff_names);
          proof_ns = (uu___126_17404.proof_ns);
          synth_hook = (uu___126_17404.synth_hook);
          splice = (uu___126_17404.splice);
          is_native_tactic = (uu___126_17404.is_native_tactic);
          identifier_info = (uu___126_17404.identifier_info);
          tc_hooks = (uu___126_17404.tc_hooks);
          dsenv = (uu___126_17404.dsenv);
          dep_graph = (uu___126_17404.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___127_17416 = env  in
      {
        solver = (uu___127_17416.solver);
        range = (uu___127_17416.range);
        curmodule = (uu___127_17416.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___127_17416.gamma_sig);
        gamma_cache = (uu___127_17416.gamma_cache);
        modules = (uu___127_17416.modules);
        expected_typ = (uu___127_17416.expected_typ);
        sigtab = (uu___127_17416.sigtab);
        is_pattern = (uu___127_17416.is_pattern);
        instantiate_imp = (uu___127_17416.instantiate_imp);
        effects = (uu___127_17416.effects);
        generalize = (uu___127_17416.generalize);
        letrecs = (uu___127_17416.letrecs);
        top_level = (uu___127_17416.top_level);
        check_uvars = (uu___127_17416.check_uvars);
        use_eq = (uu___127_17416.use_eq);
        is_iface = (uu___127_17416.is_iface);
        admit = (uu___127_17416.admit);
        lax = (uu___127_17416.lax);
        lax_universes = (uu___127_17416.lax_universes);
        failhard = (uu___127_17416.failhard);
        nosynth = (uu___127_17416.nosynth);
        uvar_subtyping = (uu___127_17416.uvar_subtyping);
        tc_term = (uu___127_17416.tc_term);
        type_of = (uu___127_17416.type_of);
        universe_of = (uu___127_17416.universe_of);
        check_type_of = (uu___127_17416.check_type_of);
        use_bv_sorts = (uu___127_17416.use_bv_sorts);
        qtbl_name_and_index = (uu___127_17416.qtbl_name_and_index);
        normalized_eff_names = (uu___127_17416.normalized_eff_names);
        proof_ns = (uu___127_17416.proof_ns);
        synth_hook = (uu___127_17416.synth_hook);
        splice = (uu___127_17416.splice);
        is_native_tactic = (uu___127_17416.is_native_tactic);
        identifier_info = (uu___127_17416.identifier_info);
        tc_hooks = (uu___127_17416.tc_hooks);
        dsenv = (uu___127_17416.dsenv);
        dep_graph = (uu___127_17416.dep_graph)
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
            (let uu___128_17471 = env  in
             {
               solver = (uu___128_17471.solver);
               range = (uu___128_17471.range);
               curmodule = (uu___128_17471.curmodule);
               gamma = rest;
               gamma_sig = (uu___128_17471.gamma_sig);
               gamma_cache = (uu___128_17471.gamma_cache);
               modules = (uu___128_17471.modules);
               expected_typ = (uu___128_17471.expected_typ);
               sigtab = (uu___128_17471.sigtab);
               is_pattern = (uu___128_17471.is_pattern);
               instantiate_imp = (uu___128_17471.instantiate_imp);
               effects = (uu___128_17471.effects);
               generalize = (uu___128_17471.generalize);
               letrecs = (uu___128_17471.letrecs);
               top_level = (uu___128_17471.top_level);
               check_uvars = (uu___128_17471.check_uvars);
               use_eq = (uu___128_17471.use_eq);
               is_iface = (uu___128_17471.is_iface);
               admit = (uu___128_17471.admit);
               lax = (uu___128_17471.lax);
               lax_universes = (uu___128_17471.lax_universes);
               failhard = (uu___128_17471.failhard);
               nosynth = (uu___128_17471.nosynth);
               uvar_subtyping = (uu___128_17471.uvar_subtyping);
               tc_term = (uu___128_17471.tc_term);
               type_of = (uu___128_17471.type_of);
               universe_of = (uu___128_17471.universe_of);
               check_type_of = (uu___128_17471.check_type_of);
               use_bv_sorts = (uu___128_17471.use_bv_sorts);
               qtbl_name_and_index = (uu___128_17471.qtbl_name_and_index);
               normalized_eff_names = (uu___128_17471.normalized_eff_names);
               proof_ns = (uu___128_17471.proof_ns);
               synth_hook = (uu___128_17471.synth_hook);
               splice = (uu___128_17471.splice);
               is_native_tactic = (uu___128_17471.is_native_tactic);
               identifier_info = (uu___128_17471.identifier_info);
               tc_hooks = (uu___128_17471.tc_hooks);
               dsenv = (uu___128_17471.dsenv);
               dep_graph = (uu___128_17471.dep_graph)
             }))
    | uu____17472 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17498  ->
             match uu____17498 with | (x,uu____17504) -> push_bv env1 x) env
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
            let uu___129_17534 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_17534.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_17534.FStar_Syntax_Syntax.index);
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
      (let uu___130_17574 = env  in
       {
         solver = (uu___130_17574.solver);
         range = (uu___130_17574.range);
         curmodule = (uu___130_17574.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___130_17574.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_17574.sigtab);
         is_pattern = (uu___130_17574.is_pattern);
         instantiate_imp = (uu___130_17574.instantiate_imp);
         effects = (uu___130_17574.effects);
         generalize = (uu___130_17574.generalize);
         letrecs = (uu___130_17574.letrecs);
         top_level = (uu___130_17574.top_level);
         check_uvars = (uu___130_17574.check_uvars);
         use_eq = (uu___130_17574.use_eq);
         is_iface = (uu___130_17574.is_iface);
         admit = (uu___130_17574.admit);
         lax = (uu___130_17574.lax);
         lax_universes = (uu___130_17574.lax_universes);
         failhard = (uu___130_17574.failhard);
         nosynth = (uu___130_17574.nosynth);
         uvar_subtyping = (uu___130_17574.uvar_subtyping);
         tc_term = (uu___130_17574.tc_term);
         type_of = (uu___130_17574.type_of);
         universe_of = (uu___130_17574.universe_of);
         check_type_of = (uu___130_17574.check_type_of);
         use_bv_sorts = (uu___130_17574.use_bv_sorts);
         qtbl_name_and_index = (uu___130_17574.qtbl_name_and_index);
         normalized_eff_names = (uu___130_17574.normalized_eff_names);
         proof_ns = (uu___130_17574.proof_ns);
         synth_hook = (uu___130_17574.synth_hook);
         splice = (uu___130_17574.splice);
         is_native_tactic = (uu___130_17574.is_native_tactic);
         identifier_info = (uu___130_17574.identifier_info);
         tc_hooks = (uu___130_17574.tc_hooks);
         dsenv = (uu___130_17574.dsenv);
         dep_graph = (uu___130_17574.dep_graph)
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
        let uu____17616 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17616 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17644 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17644)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___131_17659 = env  in
      {
        solver = (uu___131_17659.solver);
        range = (uu___131_17659.range);
        curmodule = (uu___131_17659.curmodule);
        gamma = (uu___131_17659.gamma);
        gamma_sig = (uu___131_17659.gamma_sig);
        gamma_cache = (uu___131_17659.gamma_cache);
        modules = (uu___131_17659.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_17659.sigtab);
        is_pattern = (uu___131_17659.is_pattern);
        instantiate_imp = (uu___131_17659.instantiate_imp);
        effects = (uu___131_17659.effects);
        generalize = (uu___131_17659.generalize);
        letrecs = (uu___131_17659.letrecs);
        top_level = (uu___131_17659.top_level);
        check_uvars = (uu___131_17659.check_uvars);
        use_eq = false;
        is_iface = (uu___131_17659.is_iface);
        admit = (uu___131_17659.admit);
        lax = (uu___131_17659.lax);
        lax_universes = (uu___131_17659.lax_universes);
        failhard = (uu___131_17659.failhard);
        nosynth = (uu___131_17659.nosynth);
        uvar_subtyping = (uu___131_17659.uvar_subtyping);
        tc_term = (uu___131_17659.tc_term);
        type_of = (uu___131_17659.type_of);
        universe_of = (uu___131_17659.universe_of);
        check_type_of = (uu___131_17659.check_type_of);
        use_bv_sorts = (uu___131_17659.use_bv_sorts);
        qtbl_name_and_index = (uu___131_17659.qtbl_name_and_index);
        normalized_eff_names = (uu___131_17659.normalized_eff_names);
        proof_ns = (uu___131_17659.proof_ns);
        synth_hook = (uu___131_17659.synth_hook);
        splice = (uu___131_17659.splice);
        is_native_tactic = (uu___131_17659.is_native_tactic);
        identifier_info = (uu___131_17659.identifier_info);
        tc_hooks = (uu___131_17659.tc_hooks);
        dsenv = (uu___131_17659.dsenv);
        dep_graph = (uu___131_17659.dep_graph)
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
    let uu____17687 = expected_typ env_  in
    ((let uu___132_17693 = env_  in
      {
        solver = (uu___132_17693.solver);
        range = (uu___132_17693.range);
        curmodule = (uu___132_17693.curmodule);
        gamma = (uu___132_17693.gamma);
        gamma_sig = (uu___132_17693.gamma_sig);
        gamma_cache = (uu___132_17693.gamma_cache);
        modules = (uu___132_17693.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_17693.sigtab);
        is_pattern = (uu___132_17693.is_pattern);
        instantiate_imp = (uu___132_17693.instantiate_imp);
        effects = (uu___132_17693.effects);
        generalize = (uu___132_17693.generalize);
        letrecs = (uu___132_17693.letrecs);
        top_level = (uu___132_17693.top_level);
        check_uvars = (uu___132_17693.check_uvars);
        use_eq = false;
        is_iface = (uu___132_17693.is_iface);
        admit = (uu___132_17693.admit);
        lax = (uu___132_17693.lax);
        lax_universes = (uu___132_17693.lax_universes);
        failhard = (uu___132_17693.failhard);
        nosynth = (uu___132_17693.nosynth);
        uvar_subtyping = (uu___132_17693.uvar_subtyping);
        tc_term = (uu___132_17693.tc_term);
        type_of = (uu___132_17693.type_of);
        universe_of = (uu___132_17693.universe_of);
        check_type_of = (uu___132_17693.check_type_of);
        use_bv_sorts = (uu___132_17693.use_bv_sorts);
        qtbl_name_and_index = (uu___132_17693.qtbl_name_and_index);
        normalized_eff_names = (uu___132_17693.normalized_eff_names);
        proof_ns = (uu___132_17693.proof_ns);
        synth_hook = (uu___132_17693.synth_hook);
        splice = (uu___132_17693.splice);
        is_native_tactic = (uu___132_17693.is_native_tactic);
        identifier_info = (uu___132_17693.identifier_info);
        tc_hooks = (uu___132_17693.tc_hooks);
        dsenv = (uu___132_17693.dsenv);
        dep_graph = (uu___132_17693.dep_graph)
      }), uu____17687)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17703 =
      let uu____17706 = FStar_Ident.id_of_text ""  in [uu____17706]  in
    FStar_Ident.lid_of_ids uu____17703  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17712 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17712
        then
          let uu____17715 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17715 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___133_17742 = env  in
       {
         solver = (uu___133_17742.solver);
         range = (uu___133_17742.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___133_17742.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_17742.expected_typ);
         sigtab = (uu___133_17742.sigtab);
         is_pattern = (uu___133_17742.is_pattern);
         instantiate_imp = (uu___133_17742.instantiate_imp);
         effects = (uu___133_17742.effects);
         generalize = (uu___133_17742.generalize);
         letrecs = (uu___133_17742.letrecs);
         top_level = (uu___133_17742.top_level);
         check_uvars = (uu___133_17742.check_uvars);
         use_eq = (uu___133_17742.use_eq);
         is_iface = (uu___133_17742.is_iface);
         admit = (uu___133_17742.admit);
         lax = (uu___133_17742.lax);
         lax_universes = (uu___133_17742.lax_universes);
         failhard = (uu___133_17742.failhard);
         nosynth = (uu___133_17742.nosynth);
         uvar_subtyping = (uu___133_17742.uvar_subtyping);
         tc_term = (uu___133_17742.tc_term);
         type_of = (uu___133_17742.type_of);
         universe_of = (uu___133_17742.universe_of);
         check_type_of = (uu___133_17742.check_type_of);
         use_bv_sorts = (uu___133_17742.use_bv_sorts);
         qtbl_name_and_index = (uu___133_17742.qtbl_name_and_index);
         normalized_eff_names = (uu___133_17742.normalized_eff_names);
         proof_ns = (uu___133_17742.proof_ns);
         synth_hook = (uu___133_17742.synth_hook);
         splice = (uu___133_17742.splice);
         is_native_tactic = (uu___133_17742.is_native_tactic);
         identifier_info = (uu___133_17742.identifier_info);
         tc_hooks = (uu___133_17742.tc_hooks);
         dsenv = (uu___133_17742.dsenv);
         dep_graph = (uu___133_17742.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17793)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17797,(uu____17798,t)))::tl1
          ->
          let uu____17819 =
            let uu____17822 = FStar_Syntax_Free.uvars t  in
            ext out uu____17822  in
          aux uu____17819 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17825;
            FStar_Syntax_Syntax.index = uu____17826;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17833 =
            let uu____17836 = FStar_Syntax_Free.uvars t  in
            ext out uu____17836  in
          aux uu____17833 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17893)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17897,(uu____17898,t)))::tl1
          ->
          let uu____17919 =
            let uu____17922 = FStar_Syntax_Free.univs t  in
            ext out uu____17922  in
          aux uu____17919 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17925;
            FStar_Syntax_Syntax.index = uu____17926;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17933 =
            let uu____17936 = FStar_Syntax_Free.univs t  in
            ext out uu____17936  in
          aux uu____17933 tl1
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
          let uu____17997 = FStar_Util.set_add uname out  in
          aux uu____17997 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18000,(uu____18001,t)))::tl1
          ->
          let uu____18022 =
            let uu____18025 = FStar_Syntax_Free.univnames t  in
            ext out uu____18025  in
          aux uu____18022 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18028;
            FStar_Syntax_Syntax.index = uu____18029;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18036 =
            let uu____18039 = FStar_Syntax_Free.univnames t  in
            ext out uu____18039  in
          aux uu____18036 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___107_18059  ->
            match uu___107_18059 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18063 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____18076 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____18086 =
      let uu____18093 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____18093
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____18086 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____18131 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___108_18141  ->
              match uu___108_18141 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____18143 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____18143
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____18146) ->
                  let uu____18163 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____18163))
       in
    FStar_All.pipe_right uu____18131 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___109_18170  ->
    match uu___109_18170 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____18171 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18191  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18233) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18252,uu____18253) -> false  in
      let uu____18262 =
        FStar_List.tryFind
          (fun uu____18280  ->
             match uu____18280 with | (p,uu____18288) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18262 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18299,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18321 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18321
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___134_18339 = e  in
        {
          solver = (uu___134_18339.solver);
          range = (uu___134_18339.range);
          curmodule = (uu___134_18339.curmodule);
          gamma = (uu___134_18339.gamma);
          gamma_sig = (uu___134_18339.gamma_sig);
          gamma_cache = (uu___134_18339.gamma_cache);
          modules = (uu___134_18339.modules);
          expected_typ = (uu___134_18339.expected_typ);
          sigtab = (uu___134_18339.sigtab);
          is_pattern = (uu___134_18339.is_pattern);
          instantiate_imp = (uu___134_18339.instantiate_imp);
          effects = (uu___134_18339.effects);
          generalize = (uu___134_18339.generalize);
          letrecs = (uu___134_18339.letrecs);
          top_level = (uu___134_18339.top_level);
          check_uvars = (uu___134_18339.check_uvars);
          use_eq = (uu___134_18339.use_eq);
          is_iface = (uu___134_18339.is_iface);
          admit = (uu___134_18339.admit);
          lax = (uu___134_18339.lax);
          lax_universes = (uu___134_18339.lax_universes);
          failhard = (uu___134_18339.failhard);
          nosynth = (uu___134_18339.nosynth);
          uvar_subtyping = (uu___134_18339.uvar_subtyping);
          tc_term = (uu___134_18339.tc_term);
          type_of = (uu___134_18339.type_of);
          universe_of = (uu___134_18339.universe_of);
          check_type_of = (uu___134_18339.check_type_of);
          use_bv_sorts = (uu___134_18339.use_bv_sorts);
          qtbl_name_and_index = (uu___134_18339.qtbl_name_and_index);
          normalized_eff_names = (uu___134_18339.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___134_18339.synth_hook);
          splice = (uu___134_18339.splice);
          is_native_tactic = (uu___134_18339.is_native_tactic);
          identifier_info = (uu___134_18339.identifier_info);
          tc_hooks = (uu___134_18339.tc_hooks);
          dsenv = (uu___134_18339.dsenv);
          dep_graph = (uu___134_18339.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___135_18379 = e  in
      {
        solver = (uu___135_18379.solver);
        range = (uu___135_18379.range);
        curmodule = (uu___135_18379.curmodule);
        gamma = (uu___135_18379.gamma);
        gamma_sig = (uu___135_18379.gamma_sig);
        gamma_cache = (uu___135_18379.gamma_cache);
        modules = (uu___135_18379.modules);
        expected_typ = (uu___135_18379.expected_typ);
        sigtab = (uu___135_18379.sigtab);
        is_pattern = (uu___135_18379.is_pattern);
        instantiate_imp = (uu___135_18379.instantiate_imp);
        effects = (uu___135_18379.effects);
        generalize = (uu___135_18379.generalize);
        letrecs = (uu___135_18379.letrecs);
        top_level = (uu___135_18379.top_level);
        check_uvars = (uu___135_18379.check_uvars);
        use_eq = (uu___135_18379.use_eq);
        is_iface = (uu___135_18379.is_iface);
        admit = (uu___135_18379.admit);
        lax = (uu___135_18379.lax);
        lax_universes = (uu___135_18379.lax_universes);
        failhard = (uu___135_18379.failhard);
        nosynth = (uu___135_18379.nosynth);
        uvar_subtyping = (uu___135_18379.uvar_subtyping);
        tc_term = (uu___135_18379.tc_term);
        type_of = (uu___135_18379.type_of);
        universe_of = (uu___135_18379.universe_of);
        check_type_of = (uu___135_18379.check_type_of);
        use_bv_sorts = (uu___135_18379.use_bv_sorts);
        qtbl_name_and_index = (uu___135_18379.qtbl_name_and_index);
        normalized_eff_names = (uu___135_18379.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___135_18379.synth_hook);
        splice = (uu___135_18379.splice);
        is_native_tactic = (uu___135_18379.is_native_tactic);
        identifier_info = (uu___135_18379.identifier_info);
        tc_hooks = (uu___135_18379.tc_hooks);
        dsenv = (uu___135_18379.dsenv);
        dep_graph = (uu___135_18379.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18394 = FStar_Syntax_Free.names t  in
      let uu____18397 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18394 uu____18397
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18418 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18418
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18426 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18426
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18443 =
      match uu____18443 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18453 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18453)
       in
    let uu____18455 =
      let uu____18458 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18458 FStar_List.rev  in
    FStar_All.pipe_right uu____18455 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18473  -> ());
    push = (fun uu____18475  -> ());
    pop = (fun uu____18477  -> ());
    snapshot =
      (fun uu____18479  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18488  -> fun uu____18489  -> ());
    encode_modul = (fun uu____18500  -> fun uu____18501  -> ());
    encode_sig = (fun uu____18504  -> fun uu____18505  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18511 =
             let uu____18518 = FStar_Options.peek ()  in (e, g, uu____18518)
              in
           [uu____18511]);
    solve = (fun uu____18534  -> fun uu____18535  -> fun uu____18536  -> ());
    finish = (fun uu____18542  -> ());
    refresh = (fun uu____18544  -> ())
  } 