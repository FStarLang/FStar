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
           (fun uu___218_8271  ->
              match uu___218_8271 with
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
                         let uu___232_8281 = y1  in
                         let uu____8282 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___232_8281.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___232_8281.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8282
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____8280
                   | uu____8285 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___233_8297 = env  in
      let uu____8298 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___233_8297.solver);
        range = (uu___233_8297.range);
        curmodule = (uu___233_8297.curmodule);
        gamma = uu____8298;
        gamma_sig = (uu___233_8297.gamma_sig);
        gamma_cache = (uu___233_8297.gamma_cache);
        modules = (uu___233_8297.modules);
        expected_typ = (uu___233_8297.expected_typ);
        sigtab = (uu___233_8297.sigtab);
        is_pattern = (uu___233_8297.is_pattern);
        instantiate_imp = (uu___233_8297.instantiate_imp);
        effects = (uu___233_8297.effects);
        generalize = (uu___233_8297.generalize);
        letrecs = (uu___233_8297.letrecs);
        top_level = (uu___233_8297.top_level);
        check_uvars = (uu___233_8297.check_uvars);
        use_eq = (uu___233_8297.use_eq);
        is_iface = (uu___233_8297.is_iface);
        admit = (uu___233_8297.admit);
        lax = (uu___233_8297.lax);
        lax_universes = (uu___233_8297.lax_universes);
        failhard = (uu___233_8297.failhard);
        nosynth = (uu___233_8297.nosynth);
        uvar_subtyping = (uu___233_8297.uvar_subtyping);
        tc_term = (uu___233_8297.tc_term);
        type_of = (uu___233_8297.type_of);
        universe_of = (uu___233_8297.universe_of);
        check_type_of = (uu___233_8297.check_type_of);
        use_bv_sorts = (uu___233_8297.use_bv_sorts);
        qtbl_name_and_index = (uu___233_8297.qtbl_name_and_index);
        normalized_eff_names = (uu___233_8297.normalized_eff_names);
        proof_ns = (uu___233_8297.proof_ns);
        synth_hook = (uu___233_8297.synth_hook);
        splice = (uu___233_8297.splice);
        is_native_tactic = (uu___233_8297.is_native_tactic);
        identifier_info = (uu___233_8297.identifier_info);
        tc_hooks = (uu___233_8297.tc_hooks);
        dsenv = (uu___233_8297.dsenv);
        dep_graph = (uu___233_8297.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8305  -> fun uu____8306  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___234_8326 = env  in
      {
        solver = (uu___234_8326.solver);
        range = (uu___234_8326.range);
        curmodule = (uu___234_8326.curmodule);
        gamma = (uu___234_8326.gamma);
        gamma_sig = (uu___234_8326.gamma_sig);
        gamma_cache = (uu___234_8326.gamma_cache);
        modules = (uu___234_8326.modules);
        expected_typ = (uu___234_8326.expected_typ);
        sigtab = (uu___234_8326.sigtab);
        is_pattern = (uu___234_8326.is_pattern);
        instantiate_imp = (uu___234_8326.instantiate_imp);
        effects = (uu___234_8326.effects);
        generalize = (uu___234_8326.generalize);
        letrecs = (uu___234_8326.letrecs);
        top_level = (uu___234_8326.top_level);
        check_uvars = (uu___234_8326.check_uvars);
        use_eq = (uu___234_8326.use_eq);
        is_iface = (uu___234_8326.is_iface);
        admit = (uu___234_8326.admit);
        lax = (uu___234_8326.lax);
        lax_universes = (uu___234_8326.lax_universes);
        failhard = (uu___234_8326.failhard);
        nosynth = (uu___234_8326.nosynth);
        uvar_subtyping = (uu___234_8326.uvar_subtyping);
        tc_term = (uu___234_8326.tc_term);
        type_of = (uu___234_8326.type_of);
        universe_of = (uu___234_8326.universe_of);
        check_type_of = (uu___234_8326.check_type_of);
        use_bv_sorts = (uu___234_8326.use_bv_sorts);
        qtbl_name_and_index = (uu___234_8326.qtbl_name_and_index);
        normalized_eff_names = (uu___234_8326.normalized_eff_names);
        proof_ns = (uu___234_8326.proof_ns);
        synth_hook = (uu___234_8326.synth_hook);
        splice = (uu___234_8326.splice);
        is_native_tactic = (uu___234_8326.is_native_tactic);
        identifier_info = (uu___234_8326.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___234_8326.dsenv);
        dep_graph = (uu___234_8326.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___235_8337 = e  in
      {
        solver = (uu___235_8337.solver);
        range = (uu___235_8337.range);
        curmodule = (uu___235_8337.curmodule);
        gamma = (uu___235_8337.gamma);
        gamma_sig = (uu___235_8337.gamma_sig);
        gamma_cache = (uu___235_8337.gamma_cache);
        modules = (uu___235_8337.modules);
        expected_typ = (uu___235_8337.expected_typ);
        sigtab = (uu___235_8337.sigtab);
        is_pattern = (uu___235_8337.is_pattern);
        instantiate_imp = (uu___235_8337.instantiate_imp);
        effects = (uu___235_8337.effects);
        generalize = (uu___235_8337.generalize);
        letrecs = (uu___235_8337.letrecs);
        top_level = (uu___235_8337.top_level);
        check_uvars = (uu___235_8337.check_uvars);
        use_eq = (uu___235_8337.use_eq);
        is_iface = (uu___235_8337.is_iface);
        admit = (uu___235_8337.admit);
        lax = (uu___235_8337.lax);
        lax_universes = (uu___235_8337.lax_universes);
        failhard = (uu___235_8337.failhard);
        nosynth = (uu___235_8337.nosynth);
        uvar_subtyping = (uu___235_8337.uvar_subtyping);
        tc_term = (uu___235_8337.tc_term);
        type_of = (uu___235_8337.type_of);
        universe_of = (uu___235_8337.universe_of);
        check_type_of = (uu___235_8337.check_type_of);
        use_bv_sorts = (uu___235_8337.use_bv_sorts);
        qtbl_name_and_index = (uu___235_8337.qtbl_name_and_index);
        normalized_eff_names = (uu___235_8337.normalized_eff_names);
        proof_ns = (uu___235_8337.proof_ns);
        synth_hook = (uu___235_8337.synth_hook);
        splice = (uu___235_8337.splice);
        is_native_tactic = (uu___235_8337.is_native_tactic);
        identifier_info = (uu___235_8337.identifier_info);
        tc_hooks = (uu___235_8337.tc_hooks);
        dsenv = (uu___235_8337.dsenv);
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
    | uu____8720 ->
        let uu____8729 =
          let uu____8738 =
            let uu____8745 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8745  in
          let uu____8795 = FStar_ST.op_Bang query_indices  in uu____8738 ::
            uu____8795
           in
        FStar_ST.op_Colon_Equals query_indices uu____8729
  
let (pop_query_indices : unit -> unit) =
  fun uu____8884  ->
    let uu____8885 = FStar_ST.op_Bang query_indices  in
    match uu____8885 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9000  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9030  ->
    match uu____9030 with
    | (l,n1) ->
        let uu____9037 = FStar_ST.op_Bang query_indices  in
        (match uu____9037 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____9148 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____9167  ->
    let uu____9168 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____9168
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9241 =
       let uu____9244 = FStar_ST.op_Bang stack  in env :: uu____9244  in
     FStar_ST.op_Colon_Equals stack uu____9241);
    (let uu___236_9293 = env  in
     let uu____9294 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9297 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9300 =
       let uu____9313 =
         let uu____9316 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9316  in
       let uu____9341 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9313, uu____9341)  in
     let uu____9382 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9385 =
       let uu____9388 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9388  in
     {
       solver = (uu___236_9293.solver);
       range = (uu___236_9293.range);
       curmodule = (uu___236_9293.curmodule);
       gamma = (uu___236_9293.gamma);
       gamma_sig = (uu___236_9293.gamma_sig);
       gamma_cache = uu____9294;
       modules = (uu___236_9293.modules);
       expected_typ = (uu___236_9293.expected_typ);
       sigtab = uu____9297;
       is_pattern = (uu___236_9293.is_pattern);
       instantiate_imp = (uu___236_9293.instantiate_imp);
       effects = (uu___236_9293.effects);
       generalize = (uu___236_9293.generalize);
       letrecs = (uu___236_9293.letrecs);
       top_level = (uu___236_9293.top_level);
       check_uvars = (uu___236_9293.check_uvars);
       use_eq = (uu___236_9293.use_eq);
       is_iface = (uu___236_9293.is_iface);
       admit = (uu___236_9293.admit);
       lax = (uu___236_9293.lax);
       lax_universes = (uu___236_9293.lax_universes);
       failhard = (uu___236_9293.failhard);
       nosynth = (uu___236_9293.nosynth);
       uvar_subtyping = (uu___236_9293.uvar_subtyping);
       tc_term = (uu___236_9293.tc_term);
       type_of = (uu___236_9293.type_of);
       universe_of = (uu___236_9293.universe_of);
       check_type_of = (uu___236_9293.check_type_of);
       use_bv_sorts = (uu___236_9293.use_bv_sorts);
       qtbl_name_and_index = uu____9300;
       normalized_eff_names = uu____9382;
       proof_ns = (uu___236_9293.proof_ns);
       synth_hook = (uu___236_9293.synth_hook);
       splice = (uu___236_9293.splice);
       is_native_tactic = (uu___236_9293.is_native_tactic);
       identifier_info = uu____9385;
       tc_hooks = (uu___236_9293.tc_hooks);
       dsenv = (uu___236_9293.dsenv);
       dep_graph = (uu___236_9293.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9434  ->
    let uu____9435 = FStar_ST.op_Bang stack  in
    match uu____9435 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9489 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____9561  ->
           let uu____9562 = snapshot_stack env  in
           match uu____9562 with
           | (stack_depth,env1) ->
               let uu____9587 = snapshot_query_indices ()  in
               (match uu____9587 with
                | (query_indices_depth,()) ->
                    let uu____9611 = (env1.solver).snapshot msg  in
                    (match uu____9611 with
                     | (solver_depth,()) ->
                         let uu____9653 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9653 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___237_9699 = env1  in
                                 {
                                   solver = (uu___237_9699.solver);
                                   range = (uu___237_9699.range);
                                   curmodule = (uu___237_9699.curmodule);
                                   gamma = (uu___237_9699.gamma);
                                   gamma_sig = (uu___237_9699.gamma_sig);
                                   gamma_cache = (uu___237_9699.gamma_cache);
                                   modules = (uu___237_9699.modules);
                                   expected_typ =
                                     (uu___237_9699.expected_typ);
                                   sigtab = (uu___237_9699.sigtab);
                                   is_pattern = (uu___237_9699.is_pattern);
                                   instantiate_imp =
                                     (uu___237_9699.instantiate_imp);
                                   effects = (uu___237_9699.effects);
                                   generalize = (uu___237_9699.generalize);
                                   letrecs = (uu___237_9699.letrecs);
                                   top_level = (uu___237_9699.top_level);
                                   check_uvars = (uu___237_9699.check_uvars);
                                   use_eq = (uu___237_9699.use_eq);
                                   is_iface = (uu___237_9699.is_iface);
                                   admit = (uu___237_9699.admit);
                                   lax = (uu___237_9699.lax);
                                   lax_universes =
                                     (uu___237_9699.lax_universes);
                                   failhard = (uu___237_9699.failhard);
                                   nosynth = (uu___237_9699.nosynth);
                                   uvar_subtyping =
                                     (uu___237_9699.uvar_subtyping);
                                   tc_term = (uu___237_9699.tc_term);
                                   type_of = (uu___237_9699.type_of);
                                   universe_of = (uu___237_9699.universe_of);
                                   check_type_of =
                                     (uu___237_9699.check_type_of);
                                   use_bv_sorts =
                                     (uu___237_9699.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___237_9699.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___237_9699.normalized_eff_names);
                                   proof_ns = (uu___237_9699.proof_ns);
                                   synth_hook = (uu___237_9699.synth_hook);
                                   splice = (uu___237_9699.splice);
                                   is_native_tactic =
                                     (uu___237_9699.is_native_tactic);
                                   identifier_info =
                                     (uu___237_9699.identifier_info);
                                   tc_hooks = (uu___237_9699.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___237_9699.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9730  ->
             let uu____9731 =
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
             match uu____9731 with
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
                             ((let uu____9857 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9857
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9868 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9868
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9895,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9927 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9953  ->
                  match uu____9953 with
                  | (m,uu____9959) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9927 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___238_9967 = env  in
               {
                 solver = (uu___238_9967.solver);
                 range = (uu___238_9967.range);
                 curmodule = (uu___238_9967.curmodule);
                 gamma = (uu___238_9967.gamma);
                 gamma_sig = (uu___238_9967.gamma_sig);
                 gamma_cache = (uu___238_9967.gamma_cache);
                 modules = (uu___238_9967.modules);
                 expected_typ = (uu___238_9967.expected_typ);
                 sigtab = (uu___238_9967.sigtab);
                 is_pattern = (uu___238_9967.is_pattern);
                 instantiate_imp = (uu___238_9967.instantiate_imp);
                 effects = (uu___238_9967.effects);
                 generalize = (uu___238_9967.generalize);
                 letrecs = (uu___238_9967.letrecs);
                 top_level = (uu___238_9967.top_level);
                 check_uvars = (uu___238_9967.check_uvars);
                 use_eq = (uu___238_9967.use_eq);
                 is_iface = (uu___238_9967.is_iface);
                 admit = (uu___238_9967.admit);
                 lax = (uu___238_9967.lax);
                 lax_universes = (uu___238_9967.lax_universes);
                 failhard = (uu___238_9967.failhard);
                 nosynth = (uu___238_9967.nosynth);
                 uvar_subtyping = (uu___238_9967.uvar_subtyping);
                 tc_term = (uu___238_9967.tc_term);
                 type_of = (uu___238_9967.type_of);
                 universe_of = (uu___238_9967.universe_of);
                 check_type_of = (uu___238_9967.check_type_of);
                 use_bv_sorts = (uu___238_9967.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___238_9967.normalized_eff_names);
                 proof_ns = (uu___238_9967.proof_ns);
                 synth_hook = (uu___238_9967.synth_hook);
                 splice = (uu___238_9967.splice);
                 is_native_tactic = (uu___238_9967.is_native_tactic);
                 identifier_info = (uu___238_9967.identifier_info);
                 tc_hooks = (uu___238_9967.tc_hooks);
                 dsenv = (uu___238_9967.dsenv);
                 dep_graph = (uu___238_9967.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9980,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___239_9989 = env  in
               {
                 solver = (uu___239_9989.solver);
                 range = (uu___239_9989.range);
                 curmodule = (uu___239_9989.curmodule);
                 gamma = (uu___239_9989.gamma);
                 gamma_sig = (uu___239_9989.gamma_sig);
                 gamma_cache = (uu___239_9989.gamma_cache);
                 modules = (uu___239_9989.modules);
                 expected_typ = (uu___239_9989.expected_typ);
                 sigtab = (uu___239_9989.sigtab);
                 is_pattern = (uu___239_9989.is_pattern);
                 instantiate_imp = (uu___239_9989.instantiate_imp);
                 effects = (uu___239_9989.effects);
                 generalize = (uu___239_9989.generalize);
                 letrecs = (uu___239_9989.letrecs);
                 top_level = (uu___239_9989.top_level);
                 check_uvars = (uu___239_9989.check_uvars);
                 use_eq = (uu___239_9989.use_eq);
                 is_iface = (uu___239_9989.is_iface);
                 admit = (uu___239_9989.admit);
                 lax = (uu___239_9989.lax);
                 lax_universes = (uu___239_9989.lax_universes);
                 failhard = (uu___239_9989.failhard);
                 nosynth = (uu___239_9989.nosynth);
                 uvar_subtyping = (uu___239_9989.uvar_subtyping);
                 tc_term = (uu___239_9989.tc_term);
                 type_of = (uu___239_9989.type_of);
                 universe_of = (uu___239_9989.universe_of);
                 check_type_of = (uu___239_9989.check_type_of);
                 use_bv_sorts = (uu___239_9989.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___239_9989.normalized_eff_names);
                 proof_ns = (uu___239_9989.proof_ns);
                 synth_hook = (uu___239_9989.synth_hook);
                 splice = (uu___239_9989.splice);
                 is_native_tactic = (uu___239_9989.is_native_tactic);
                 identifier_info = (uu___239_9989.identifier_info);
                 tc_hooks = (uu___239_9989.tc_hooks);
                 dsenv = (uu___239_9989.dsenv);
                 dep_graph = (uu___239_9989.dep_graph)
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
        (let uu___240_10023 = e  in
         {
           solver = (uu___240_10023.solver);
           range = r;
           curmodule = (uu___240_10023.curmodule);
           gamma = (uu___240_10023.gamma);
           gamma_sig = (uu___240_10023.gamma_sig);
           gamma_cache = (uu___240_10023.gamma_cache);
           modules = (uu___240_10023.modules);
           expected_typ = (uu___240_10023.expected_typ);
           sigtab = (uu___240_10023.sigtab);
           is_pattern = (uu___240_10023.is_pattern);
           instantiate_imp = (uu___240_10023.instantiate_imp);
           effects = (uu___240_10023.effects);
           generalize = (uu___240_10023.generalize);
           letrecs = (uu___240_10023.letrecs);
           top_level = (uu___240_10023.top_level);
           check_uvars = (uu___240_10023.check_uvars);
           use_eq = (uu___240_10023.use_eq);
           is_iface = (uu___240_10023.is_iface);
           admit = (uu___240_10023.admit);
           lax = (uu___240_10023.lax);
           lax_universes = (uu___240_10023.lax_universes);
           failhard = (uu___240_10023.failhard);
           nosynth = (uu___240_10023.nosynth);
           uvar_subtyping = (uu___240_10023.uvar_subtyping);
           tc_term = (uu___240_10023.tc_term);
           type_of = (uu___240_10023.type_of);
           universe_of = (uu___240_10023.universe_of);
           check_type_of = (uu___240_10023.check_type_of);
           use_bv_sorts = (uu___240_10023.use_bv_sorts);
           qtbl_name_and_index = (uu___240_10023.qtbl_name_and_index);
           normalized_eff_names = (uu___240_10023.normalized_eff_names);
           proof_ns = (uu___240_10023.proof_ns);
           synth_hook = (uu___240_10023.synth_hook);
           splice = (uu___240_10023.splice);
           is_native_tactic = (uu___240_10023.is_native_tactic);
           identifier_info = (uu___240_10023.identifier_info);
           tc_hooks = (uu___240_10023.tc_hooks);
           dsenv = (uu___240_10023.dsenv);
           dep_graph = (uu___240_10023.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10039 =
        let uu____10040 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10040 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10039
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10094 =
          let uu____10095 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10095 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10094
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10149 =
          let uu____10150 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10150 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10149
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10204 =
        let uu____10205 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10205 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10204
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___241_10266 = env  in
      {
        solver = (uu___241_10266.solver);
        range = (uu___241_10266.range);
        curmodule = lid;
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
      let uu____10293 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10293
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10303 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10303)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10313 =
      let uu____10314 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10314  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10313)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10319  ->
    let uu____10320 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10320
  
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
      | ((formals,t),uu____10376) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10410 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10410)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___219_10426  ->
    match uu___219_10426 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10452  -> new_u_univ ()))
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
      let uu____10471 = inst_tscheme t  in
      match uu____10471 with
      | (us,t1) ->
          let uu____10482 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10482)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10502  ->
          match uu____10502 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10521 =
                         let uu____10522 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10523 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10524 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10525 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10522 uu____10523 uu____10524 uu____10525
                          in
                       failwith uu____10521)
                    else ();
                    (let uu____10527 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10527))
               | uu____10536 ->
                   let uu____10537 =
                     let uu____10538 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10538
                      in
                   failwith uu____10537)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10544 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10550 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10556 -> false
  
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
             | ([],uu____10598) -> Maybe
             | (uu____10605,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10624 -> No  in
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
          let uu____10715 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10715 with
          | FStar_Pervasives_Native.None  ->
              let uu____10738 =
                FStar_Util.find_map env.gamma
                  (fun uu___220_10782  ->
                     match uu___220_10782 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____10821 = FStar_Ident.lid_equals lid l  in
                         if uu____10821
                         then
                           let uu____10842 =
                             let uu____10861 =
                               let uu____10876 = inst_tscheme t  in
                               FStar_Util.Inl uu____10876  in
                             let uu____10891 = FStar_Ident.range_of_lid l  in
                             (uu____10861, uu____10891)  in
                           FStar_Pervasives_Native.Some uu____10842
                         else FStar_Pervasives_Native.None
                     | uu____10943 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____10738
                (fun uu____10981  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___221_10990  ->
                        match uu___221_10990 with
                        | (uu____10993,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____10995);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____10996;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____10997;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____10998;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____10999;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11019 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11019
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
                                  uu____11067 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11074 -> cache t  in
                            let uu____11075 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11075 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11081 =
                                   let uu____11082 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11082)
                                    in
                                 maybe_cache uu____11081)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11150 = find_in_sigtab env lid  in
         match uu____11150 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11237) ->
          add_sigelts env ses
      | uu____11246 ->
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
            | uu____11260 -> ()))

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
        (fun uu___222_11291  ->
           match uu___222_11291 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11309 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11370,lb::[]),uu____11372) ->
            let uu____11379 =
              let uu____11388 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11397 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11388, uu____11397)  in
            FStar_Pervasives_Native.Some uu____11379
        | FStar_Syntax_Syntax.Sig_let ((uu____11410,lbs),uu____11412) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11442 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11454 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11454
                     then
                       let uu____11465 =
                         let uu____11474 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11483 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11474, uu____11483)  in
                       FStar_Pervasives_Native.Some uu____11465
                     else FStar_Pervasives_Native.None)
        | uu____11505 -> FStar_Pervasives_Native.None
  
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
          let uu____11564 =
            let uu____11573 =
              let uu____11578 =
                let uu____11579 =
                  let uu____11582 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11582
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11579)  in
              inst_tscheme1 uu____11578  in
            (uu____11573, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11564
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11604,uu____11605) ->
          let uu____11610 =
            let uu____11619 =
              let uu____11624 =
                let uu____11625 =
                  let uu____11628 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11628  in
                (us, uu____11625)  in
              inst_tscheme1 uu____11624  in
            (uu____11619, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11610
      | uu____11647 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11735 =
          match uu____11735 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11831,uvs,t,uu____11834,uu____11835,uu____11836);
                      FStar_Syntax_Syntax.sigrng = uu____11837;
                      FStar_Syntax_Syntax.sigquals = uu____11838;
                      FStar_Syntax_Syntax.sigmeta = uu____11839;
                      FStar_Syntax_Syntax.sigattrs = uu____11840;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11861 =
                     let uu____11870 = inst_tscheme1 (uvs, t)  in
                     (uu____11870, rng)  in
                   FStar_Pervasives_Native.Some uu____11861
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11894;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11896;
                      FStar_Syntax_Syntax.sigattrs = uu____11897;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11914 =
                     let uu____11915 = in_cur_mod env l  in uu____11915 = Yes
                      in
                   if uu____11914
                   then
                     let uu____11926 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____11926
                      then
                        let uu____11939 =
                          let uu____11948 = inst_tscheme1 (uvs, t)  in
                          (uu____11948, rng)  in
                        FStar_Pervasives_Native.Some uu____11939
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____11979 =
                        let uu____11988 = inst_tscheme1 (uvs, t)  in
                        (uu____11988, rng)  in
                      FStar_Pervasives_Native.Some uu____11979)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12013,uu____12014);
                      FStar_Syntax_Syntax.sigrng = uu____12015;
                      FStar_Syntax_Syntax.sigquals = uu____12016;
                      FStar_Syntax_Syntax.sigmeta = uu____12017;
                      FStar_Syntax_Syntax.sigattrs = uu____12018;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12057 =
                          let uu____12066 = inst_tscheme1 (uvs, k)  in
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
                            inst_tscheme1 uu____12102  in
                          (uu____12097, rng)  in
                        FStar_Pervasives_Native.Some uu____12088)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12129,uu____12130);
                      FStar_Syntax_Syntax.sigrng = uu____12131;
                      FStar_Syntax_Syntax.sigquals = uu____12132;
                      FStar_Syntax_Syntax.sigmeta = uu____12133;
                      FStar_Syntax_Syntax.sigattrs = uu____12134;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12174 =
                          let uu____12183 = inst_tscheme_with (uvs, k) us  in
                          (uu____12183, rng)  in
                        FStar_Pervasives_Native.Some uu____12174
                    | uu____12204 ->
                        let uu____12205 =
                          let uu____12214 =
                            let uu____12219 =
                              let uu____12220 =
                                let uu____12223 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12223
                                 in
                              (uvs, uu____12220)  in
                            inst_tscheme_with uu____12219 us  in
                          (uu____12214, rng)  in
                        FStar_Pervasives_Native.Some uu____12205)
               | FStar_Util.Inr se ->
                   let uu____12259 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12280;
                          FStar_Syntax_Syntax.sigrng = uu____12281;
                          FStar_Syntax_Syntax.sigquals = uu____12282;
                          FStar_Syntax_Syntax.sigmeta = uu____12283;
                          FStar_Syntax_Syntax.sigattrs = uu____12284;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12299 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12259
                     (FStar_Util.map_option
                        (fun uu____12347  ->
                           match uu____12347 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12378 =
          let uu____12389 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12389 mapper  in
        match uu____12378 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12463 =
              let uu____12474 =
                let uu____12481 =
                  let uu___242_12484 = t  in
                  let uu____12485 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___242_12484.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12485;
                    FStar_Syntax_Syntax.vars =
                      (uu___242_12484.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12481)  in
              (uu____12474, r)  in
            FStar_Pervasives_Native.Some uu____12463
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12532 = lookup_qname env l  in
      match uu____12532 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12551 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12603 = try_lookup_bv env bv  in
      match uu____12603 with
      | FStar_Pervasives_Native.None  ->
          let uu____12618 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12618 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12633 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12634 =
            let uu____12635 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12635  in
          (uu____12633, uu____12634)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12656 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12656 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12722 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12722  in
          let uu____12723 =
            let uu____12732 =
              let uu____12737 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12737)  in
            (uu____12732, r1)  in
          FStar_Pervasives_Native.Some uu____12723
  
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
        let uu____12771 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12771 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12804,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12829 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12829  in
            let uu____12830 =
              let uu____12835 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12835, r1)  in
            FStar_Pervasives_Native.Some uu____12830
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12858 = try_lookup_lid env l  in
      match uu____12858 with
      | FStar_Pervasives_Native.None  ->
          let uu____12885 = name_not_found l  in
          let uu____12890 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12885 uu____12890
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___223_12930  ->
              match uu___223_12930 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12932 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12951 = lookup_qname env lid  in
      match uu____12951 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12960,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12963;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12965;
              FStar_Syntax_Syntax.sigattrs = uu____12966;_},FStar_Pervasives_Native.None
            ),uu____12967)
          ->
          let uu____13016 =
            let uu____13023 =
              let uu____13024 =
                let uu____13027 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13027 t  in
              (uvs, uu____13024)  in
            (uu____13023, q)  in
          FStar_Pervasives_Native.Some uu____13016
      | uu____13040 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13061 = lookup_qname env lid  in
      match uu____13061 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13066,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13069;
              FStar_Syntax_Syntax.sigquals = uu____13070;
              FStar_Syntax_Syntax.sigmeta = uu____13071;
              FStar_Syntax_Syntax.sigattrs = uu____13072;_},FStar_Pervasives_Native.None
            ),uu____13073)
          ->
          let uu____13122 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13122 (uvs, t)
      | uu____13127 ->
          let uu____13128 = name_not_found lid  in
          let uu____13133 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13128 uu____13133
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13152 = lookup_qname env lid  in
      match uu____13152 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13157,uvs,t,uu____13160,uu____13161,uu____13162);
              FStar_Syntax_Syntax.sigrng = uu____13163;
              FStar_Syntax_Syntax.sigquals = uu____13164;
              FStar_Syntax_Syntax.sigmeta = uu____13165;
              FStar_Syntax_Syntax.sigattrs = uu____13166;_},FStar_Pervasives_Native.None
            ),uu____13167)
          ->
          let uu____13220 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13220 (uvs, t)
      | uu____13225 ->
          let uu____13226 = name_not_found lid  in
          let uu____13231 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13226 uu____13231
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13252 = lookup_qname env lid  in
      match uu____13252 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13259,uu____13260,uu____13261,uu____13262,uu____13263,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13265;
              FStar_Syntax_Syntax.sigquals = uu____13266;
              FStar_Syntax_Syntax.sigmeta = uu____13267;
              FStar_Syntax_Syntax.sigattrs = uu____13268;_},uu____13269),uu____13270)
          -> (true, dcs)
      | uu____13331 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13344 = lookup_qname env lid  in
      match uu____13344 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13345,uu____13346,uu____13347,l,uu____13349,uu____13350);
              FStar_Syntax_Syntax.sigrng = uu____13351;
              FStar_Syntax_Syntax.sigquals = uu____13352;
              FStar_Syntax_Syntax.sigmeta = uu____13353;
              FStar_Syntax_Syntax.sigattrs = uu____13354;_},uu____13355),uu____13356)
          -> l
      | uu____13411 ->
          let uu____13412 =
            let uu____13413 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13413  in
          failwith uu____13412
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13462)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13513,lbs),uu____13515)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13537 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13537
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13569 -> FStar_Pervasives_Native.None)
        | uu____13574 -> FStar_Pervasives_Native.None
  
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
        let uu____13604 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13604
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13629),uu____13630) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13679 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13700 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13700
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13719 = lookup_qname env ftv  in
      match uu____13719 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13723) ->
          let uu____13768 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13768 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13789,t),r) ->
               let uu____13804 =
                 let uu____13805 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13805 t  in
               FStar_Pervasives_Native.Some uu____13804)
      | uu____13806 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13817 = try_lookup_effect_lid env ftv  in
      match uu____13817 with
      | FStar_Pervasives_Native.None  ->
          let uu____13820 = name_not_found ftv  in
          let uu____13825 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13820 uu____13825
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
        let uu____13848 = lookup_qname env lid0  in
        match uu____13848 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13859);
                FStar_Syntax_Syntax.sigrng = uu____13860;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13862;
                FStar_Syntax_Syntax.sigattrs = uu____13863;_},FStar_Pervasives_Native.None
              ),uu____13864)
            ->
            let lid1 =
              let uu____13918 =
                let uu____13919 = FStar_Ident.range_of_lid lid  in
                let uu____13920 =
                  let uu____13921 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____13921  in
                FStar_Range.set_use_range uu____13919 uu____13920  in
              FStar_Ident.set_lid_range lid uu____13918  in
            let uu____13922 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___224_13926  ->
                      match uu___224_13926 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13927 -> false))
               in
            if uu____13922
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13941 =
                      let uu____13942 =
                        let uu____13943 = get_range env  in
                        FStar_Range.string_of_range uu____13943  in
                      let uu____13944 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____13945 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13942 uu____13944 uu____13945
                       in
                    failwith uu____13941)
                  in
               match (binders, univs1) with
               | ([],uu____13960) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____13981,uu____13982::uu____13983::uu____13984) ->
                   let uu____14001 =
                     let uu____14002 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14003 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14002 uu____14003
                      in
                   failwith uu____14001
               | uu____14010 ->
                   let uu____14023 =
                     let uu____14028 =
                       let uu____14029 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14029)  in
                     inst_tscheme_with uu____14028 insts  in
                   (match uu____14023 with
                    | (uu____14042,t) ->
                        let t1 =
                          let uu____14045 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14045 t  in
                        let uu____14046 =
                          let uu____14047 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14047.FStar_Syntax_Syntax.n  in
                        (match uu____14046 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14078 -> failwith "Impossible")))
        | uu____14085 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14108 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14108 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14121,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14128 = find1 l2  in
            (match uu____14128 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14135 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14135 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14139 = find1 l  in
            (match uu____14139 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14144 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14144
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14158 = lookup_qname env l1  in
      match uu____14158 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14161;
              FStar_Syntax_Syntax.sigrng = uu____14162;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14164;
              FStar_Syntax_Syntax.sigattrs = uu____14165;_},uu____14166),uu____14167)
          -> q
      | uu____14218 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14239 =
          let uu____14240 =
            let uu____14241 = FStar_Util.string_of_int i  in
            let uu____14242 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14241 uu____14242
             in
          failwith uu____14240  in
        let uu____14243 = lookup_datacon env lid  in
        match uu____14243 with
        | (uu____14248,t) ->
            let uu____14250 =
              let uu____14251 = FStar_Syntax_Subst.compress t  in
              uu____14251.FStar_Syntax_Syntax.n  in
            (match uu____14250 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14255) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14286 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14286
                      FStar_Pervasives_Native.fst)
             | uu____14295 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14306 = lookup_qname env l  in
      match uu____14306 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14307,uu____14308,uu____14309);
              FStar_Syntax_Syntax.sigrng = uu____14310;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14312;
              FStar_Syntax_Syntax.sigattrs = uu____14313;_},uu____14314),uu____14315)
          ->
          FStar_Util.for_some
            (fun uu___225_14368  ->
               match uu___225_14368 with
               | FStar_Syntax_Syntax.Projector uu____14369 -> true
               | uu____14374 -> false) quals
      | uu____14375 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14386 = lookup_qname env lid  in
      match uu____14386 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14387,uu____14388,uu____14389,uu____14390,uu____14391,uu____14392);
              FStar_Syntax_Syntax.sigrng = uu____14393;
              FStar_Syntax_Syntax.sigquals = uu____14394;
              FStar_Syntax_Syntax.sigmeta = uu____14395;
              FStar_Syntax_Syntax.sigattrs = uu____14396;_},uu____14397),uu____14398)
          -> true
      | uu____14453 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14464 = lookup_qname env lid  in
      match uu____14464 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14465,uu____14466,uu____14467,uu____14468,uu____14469,uu____14470);
              FStar_Syntax_Syntax.sigrng = uu____14471;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14473;
              FStar_Syntax_Syntax.sigattrs = uu____14474;_},uu____14475),uu____14476)
          ->
          FStar_Util.for_some
            (fun uu___226_14537  ->
               match uu___226_14537 with
               | FStar_Syntax_Syntax.RecordType uu____14538 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14547 -> true
               | uu____14556 -> false) quals
      | uu____14557 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14563,uu____14564);
            FStar_Syntax_Syntax.sigrng = uu____14565;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14567;
            FStar_Syntax_Syntax.sigattrs = uu____14568;_},uu____14569),uu____14570)
        ->
        FStar_Util.for_some
          (fun uu___227_14627  ->
             match uu___227_14627 with
             | FStar_Syntax_Syntax.Action uu____14628 -> true
             | uu____14629 -> false) quals
    | uu____14630 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14641 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14641
  
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
      let uu____14655 =
        let uu____14656 = FStar_Syntax_Util.un_uinst head1  in
        uu____14656.FStar_Syntax_Syntax.n  in
      match uu____14655 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14660 ->
               true
           | uu____14661 -> false)
      | uu____14662 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14673 = lookup_qname env l  in
      match uu____14673 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14675),uu____14676) ->
          FStar_Util.for_some
            (fun uu___228_14724  ->
               match uu___228_14724 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14725 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14726 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14797 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14813) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14830 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14837 ->
                 FStar_Pervasives_Native.Some true
             | uu____14854 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14855 =
        let uu____14858 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14858 mapper  in
      match uu____14855 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14908 = lookup_qname env lid  in
      match uu____14908 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14909,uu____14910,tps,uu____14912,uu____14913,uu____14914);
              FStar_Syntax_Syntax.sigrng = uu____14915;
              FStar_Syntax_Syntax.sigquals = uu____14916;
              FStar_Syntax_Syntax.sigmeta = uu____14917;
              FStar_Syntax_Syntax.sigattrs = uu____14918;_},uu____14919),uu____14920)
          -> FStar_List.length tps
      | uu____14983 ->
          let uu____14984 = name_not_found lid  in
          let uu____14989 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14984 uu____14989
  
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
           (fun uu____15033  ->
              match uu____15033 with
              | (d,uu____15041) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15056 = effect_decl_opt env l  in
      match uu____15056 with
      | FStar_Pervasives_Native.None  ->
          let uu____15071 = name_not_found l  in
          let uu____15076 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15071 uu____15076
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15098  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15117  ->
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
        let uu____15148 = FStar_Ident.lid_equals l1 l2  in
        if uu____15148
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15156 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15156
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15164 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15217  ->
                        match uu____15217 with
                        | (m1,m2,uu____15230,uu____15231,uu____15232) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15164 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15249 =
                    let uu____15254 =
                      let uu____15255 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15256 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15255
                        uu____15256
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15254)
                     in
                  FStar_Errors.raise_error uu____15249 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15263,uu____15264,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15297 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15297
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
  'Auu____15313 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15313)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15342 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15368  ->
                match uu____15368 with
                | (d,uu____15374) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15342 with
      | FStar_Pervasives_Native.None  ->
          let uu____15385 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15385
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15398 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15398 with
           | (uu____15413,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15429)::(wp,uu____15431)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15467 -> failwith "Impossible"))
  
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
          let uu____15520 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15520
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15522 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15522
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
                  let uu____15530 = get_range env  in
                  let uu____15531 =
                    let uu____15538 =
                      let uu____15539 =
                        let uu____15554 =
                          let uu____15563 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15563]  in
                        (null_wp, uu____15554)  in
                      FStar_Syntax_Syntax.Tm_app uu____15539  in
                    FStar_Syntax_Syntax.mk uu____15538  in
                  uu____15531 FStar_Pervasives_Native.None uu____15530  in
                let uu____15595 =
                  let uu____15596 =
                    let uu____15605 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15605]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15596;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15595))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___243_15636 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___243_15636.order);
              joins = (uu___243_15636.joins)
            }  in
          let uu___244_15645 = env  in
          {
            solver = (uu___244_15645.solver);
            range = (uu___244_15645.range);
            curmodule = (uu___244_15645.curmodule);
            gamma = (uu___244_15645.gamma);
            gamma_sig = (uu___244_15645.gamma_sig);
            gamma_cache = (uu___244_15645.gamma_cache);
            modules = (uu___244_15645.modules);
            expected_typ = (uu___244_15645.expected_typ);
            sigtab = (uu___244_15645.sigtab);
            is_pattern = (uu___244_15645.is_pattern);
            instantiate_imp = (uu___244_15645.instantiate_imp);
            effects;
            generalize = (uu___244_15645.generalize);
            letrecs = (uu___244_15645.letrecs);
            top_level = (uu___244_15645.top_level);
            check_uvars = (uu___244_15645.check_uvars);
            use_eq = (uu___244_15645.use_eq);
            is_iface = (uu___244_15645.is_iface);
            admit = (uu___244_15645.admit);
            lax = (uu___244_15645.lax);
            lax_universes = (uu___244_15645.lax_universes);
            failhard = (uu___244_15645.failhard);
            nosynth = (uu___244_15645.nosynth);
            uvar_subtyping = (uu___244_15645.uvar_subtyping);
            tc_term = (uu___244_15645.tc_term);
            type_of = (uu___244_15645.type_of);
            universe_of = (uu___244_15645.universe_of);
            check_type_of = (uu___244_15645.check_type_of);
            use_bv_sorts = (uu___244_15645.use_bv_sorts);
            qtbl_name_and_index = (uu___244_15645.qtbl_name_and_index);
            normalized_eff_names = (uu___244_15645.normalized_eff_names);
            proof_ns = (uu___244_15645.proof_ns);
            synth_hook = (uu___244_15645.synth_hook);
            splice = (uu___244_15645.splice);
            is_native_tactic = (uu___244_15645.is_native_tactic);
            identifier_info = (uu___244_15645.identifier_info);
            tc_hooks = (uu___244_15645.tc_hooks);
            dsenv = (uu___244_15645.dsenv);
            dep_graph = (uu___244_15645.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15675 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15675  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15833 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15834 = l1 u t wp e  in
                                l2 u t uu____15833 uu____15834))
                | uu____15835 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15907 = inst_tscheme_with lift_t [u]  in
            match uu____15907 with
            | (uu____15914,lift_t1) ->
                let uu____15916 =
                  let uu____15923 =
                    let uu____15924 =
                      let uu____15939 =
                        let uu____15948 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15955 =
                          let uu____15964 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____15964]  in
                        uu____15948 :: uu____15955  in
                      (lift_t1, uu____15939)  in
                    FStar_Syntax_Syntax.Tm_app uu____15924  in
                  FStar_Syntax_Syntax.mk uu____15923  in
                uu____15916 FStar_Pervasives_Native.None
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
            let uu____16066 = inst_tscheme_with lift_t [u]  in
            match uu____16066 with
            | (uu____16073,lift_t1) ->
                let uu____16075 =
                  let uu____16082 =
                    let uu____16083 =
                      let uu____16098 =
                        let uu____16107 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16114 =
                          let uu____16123 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16130 =
                            let uu____16139 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16139]  in
                          uu____16123 :: uu____16130  in
                        uu____16107 :: uu____16114  in
                      (lift_t1, uu____16098)  in
                    FStar_Syntax_Syntax.Tm_app uu____16083  in
                  FStar_Syntax_Syntax.mk uu____16082  in
                uu____16075 FStar_Pervasives_Native.None
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
              let uu____16229 =
                let uu____16230 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16230
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16229  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16234 =
              let uu____16235 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16235  in
            let uu____16236 =
              let uu____16237 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16263 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16263)
                 in
              FStar_Util.dflt "none" uu____16237  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16234
              uu____16236
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16289  ->
                    match uu____16289 with
                    | (e,uu____16297) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16320 =
            match uu____16320 with
            | (i,j) ->
                let uu____16331 = FStar_Ident.lid_equals i j  in
                if uu____16331
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
              let uu____16363 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16373 = FStar_Ident.lid_equals i k  in
                        if uu____16373
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16384 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16384
                                  then []
                                  else
                                    (let uu____16388 =
                                       let uu____16397 =
                                         find_edge order1 (i, k)  in
                                       let uu____16400 =
                                         find_edge order1 (k, j)  in
                                       (uu____16397, uu____16400)  in
                                     match uu____16388 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16415 =
                                           compose_edges e1 e2  in
                                         [uu____16415]
                                     | uu____16416 -> [])))))
                 in
              FStar_List.append order1 uu____16363  in
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
                   let uu____16446 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16448 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16448
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16446
                   then
                     let uu____16453 =
                       let uu____16458 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16458)
                        in
                     let uu____16459 = get_range env  in
                     FStar_Errors.raise_error uu____16453 uu____16459
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16536 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16536
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16585 =
                                              let uu____16594 =
                                                find_edge order2 (i, k)  in
                                              let uu____16597 =
                                                find_edge order2 (j, k)  in
                                              (uu____16594, uu____16597)  in
                                            match uu____16585 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16639,uu____16640)
                                                     ->
                                                     let uu____16647 =
                                                       let uu____16652 =
                                                         let uu____16653 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16653
                                                          in
                                                       let uu____16656 =
                                                         let uu____16657 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16657
                                                          in
                                                       (uu____16652,
                                                         uu____16656)
                                                        in
                                                     (match uu____16647 with
                                                      | (true ,true ) ->
                                                          let uu____16668 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16668
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
                                            | uu____16693 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___245_16766 = env.effects  in
              { decls = (uu___245_16766.decls); order = order2; joins }  in
            let uu___246_16767 = env  in
            {
              solver = (uu___246_16767.solver);
              range = (uu___246_16767.range);
              curmodule = (uu___246_16767.curmodule);
              gamma = (uu___246_16767.gamma);
              gamma_sig = (uu___246_16767.gamma_sig);
              gamma_cache = (uu___246_16767.gamma_cache);
              modules = (uu___246_16767.modules);
              expected_typ = (uu___246_16767.expected_typ);
              sigtab = (uu___246_16767.sigtab);
              is_pattern = (uu___246_16767.is_pattern);
              instantiate_imp = (uu___246_16767.instantiate_imp);
              effects;
              generalize = (uu___246_16767.generalize);
              letrecs = (uu___246_16767.letrecs);
              top_level = (uu___246_16767.top_level);
              check_uvars = (uu___246_16767.check_uvars);
              use_eq = (uu___246_16767.use_eq);
              is_iface = (uu___246_16767.is_iface);
              admit = (uu___246_16767.admit);
              lax = (uu___246_16767.lax);
              lax_universes = (uu___246_16767.lax_universes);
              failhard = (uu___246_16767.failhard);
              nosynth = (uu___246_16767.nosynth);
              uvar_subtyping = (uu___246_16767.uvar_subtyping);
              tc_term = (uu___246_16767.tc_term);
              type_of = (uu___246_16767.type_of);
              universe_of = (uu___246_16767.universe_of);
              check_type_of = (uu___246_16767.check_type_of);
              use_bv_sorts = (uu___246_16767.use_bv_sorts);
              qtbl_name_and_index = (uu___246_16767.qtbl_name_and_index);
              normalized_eff_names = (uu___246_16767.normalized_eff_names);
              proof_ns = (uu___246_16767.proof_ns);
              synth_hook = (uu___246_16767.synth_hook);
              splice = (uu___246_16767.splice);
              is_native_tactic = (uu___246_16767.is_native_tactic);
              identifier_info = (uu___246_16767.identifier_info);
              tc_hooks = (uu___246_16767.tc_hooks);
              dsenv = (uu___246_16767.dsenv);
              dep_graph = (uu___246_16767.dep_graph)
            }))
      | uu____16768 -> env
  
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
        | uu____16796 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16808 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16808 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16825 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16825 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16843 =
                     let uu____16848 =
                       let uu____16849 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16854 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16861 =
                         let uu____16862 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16862  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16849 uu____16854 uu____16861
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16848)
                      in
                   FStar_Errors.raise_error uu____16843
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16867 =
                     let uu____16876 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16876 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16905  ->
                        fun uu____16906  ->
                          match (uu____16905, uu____16906) with
                          | ((x,uu____16928),(t,uu____16930)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16867
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____16949 =
                     let uu___247_16950 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___247_16950.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___247_16950.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___247_16950.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___247_16950.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____16949
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
          let uu____16980 = effect_decl_opt env effect_name  in
          match uu____16980 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17013 =
                only_reifiable &&
                  (let uu____17015 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17015)
                 in
              if uu____17013
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17031 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____17050 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____17079 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____17079
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____17080 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____17080
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____17092 =
                       let uu____17095 = get_range env  in
                       let uu____17096 =
                         let uu____17103 =
                           let uu____17104 =
                             let uu____17119 =
                               let uu____17128 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17128; wp]  in
                             (repr, uu____17119)  in
                           FStar_Syntax_Syntax.Tm_app uu____17104  in
                         FStar_Syntax_Syntax.mk uu____17103  in
                       uu____17096 FStar_Pervasives_Native.None uu____17095
                        in
                     FStar_Pervasives_Native.Some uu____17092)
  
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
          let uu____17208 =
            let uu____17213 =
              let uu____17214 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17214
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17213)  in
          let uu____17215 = get_range env  in
          FStar_Errors.raise_error uu____17208 uu____17215  in
        let uu____17216 = effect_repr_aux true env c u_c  in
        match uu____17216 with
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
      | uu____17262 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17273 =
        let uu____17274 = FStar_Syntax_Subst.compress t  in
        uu____17274.FStar_Syntax_Syntax.n  in
      match uu____17273 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17277,c) ->
          is_reifiable_comp env c
      | uu____17295 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___248_17316 = env  in
        {
          solver = (uu___248_17316.solver);
          range = (uu___248_17316.range);
          curmodule = (uu___248_17316.curmodule);
          gamma = (uu___248_17316.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___248_17316.gamma_cache);
          modules = (uu___248_17316.modules);
          expected_typ = (uu___248_17316.expected_typ);
          sigtab = (uu___248_17316.sigtab);
          is_pattern = (uu___248_17316.is_pattern);
          instantiate_imp = (uu___248_17316.instantiate_imp);
          effects = (uu___248_17316.effects);
          generalize = (uu___248_17316.generalize);
          letrecs = (uu___248_17316.letrecs);
          top_level = (uu___248_17316.top_level);
          check_uvars = (uu___248_17316.check_uvars);
          use_eq = (uu___248_17316.use_eq);
          is_iface = (uu___248_17316.is_iface);
          admit = (uu___248_17316.admit);
          lax = (uu___248_17316.lax);
          lax_universes = (uu___248_17316.lax_universes);
          failhard = (uu___248_17316.failhard);
          nosynth = (uu___248_17316.nosynth);
          uvar_subtyping = (uu___248_17316.uvar_subtyping);
          tc_term = (uu___248_17316.tc_term);
          type_of = (uu___248_17316.type_of);
          universe_of = (uu___248_17316.universe_of);
          check_type_of = (uu___248_17316.check_type_of);
          use_bv_sorts = (uu___248_17316.use_bv_sorts);
          qtbl_name_and_index = (uu___248_17316.qtbl_name_and_index);
          normalized_eff_names = (uu___248_17316.normalized_eff_names);
          proof_ns = (uu___248_17316.proof_ns);
          synth_hook = (uu___248_17316.synth_hook);
          splice = (uu___248_17316.splice);
          is_native_tactic = (uu___248_17316.is_native_tactic);
          identifier_info = (uu___248_17316.identifier_info);
          tc_hooks = (uu___248_17316.tc_hooks);
          dsenv = (uu___248_17316.dsenv);
          dep_graph = (uu___248_17316.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___249_17328 = env  in
      {
        solver = (uu___249_17328.solver);
        range = (uu___249_17328.range);
        curmodule = (uu___249_17328.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___249_17328.gamma_sig);
        gamma_cache = (uu___249_17328.gamma_cache);
        modules = (uu___249_17328.modules);
        expected_typ = (uu___249_17328.expected_typ);
        sigtab = (uu___249_17328.sigtab);
        is_pattern = (uu___249_17328.is_pattern);
        instantiate_imp = (uu___249_17328.instantiate_imp);
        effects = (uu___249_17328.effects);
        generalize = (uu___249_17328.generalize);
        letrecs = (uu___249_17328.letrecs);
        top_level = (uu___249_17328.top_level);
        check_uvars = (uu___249_17328.check_uvars);
        use_eq = (uu___249_17328.use_eq);
        is_iface = (uu___249_17328.is_iface);
        admit = (uu___249_17328.admit);
        lax = (uu___249_17328.lax);
        lax_universes = (uu___249_17328.lax_universes);
        failhard = (uu___249_17328.failhard);
        nosynth = (uu___249_17328.nosynth);
        uvar_subtyping = (uu___249_17328.uvar_subtyping);
        tc_term = (uu___249_17328.tc_term);
        type_of = (uu___249_17328.type_of);
        universe_of = (uu___249_17328.universe_of);
        check_type_of = (uu___249_17328.check_type_of);
        use_bv_sorts = (uu___249_17328.use_bv_sorts);
        qtbl_name_and_index = (uu___249_17328.qtbl_name_and_index);
        normalized_eff_names = (uu___249_17328.normalized_eff_names);
        proof_ns = (uu___249_17328.proof_ns);
        synth_hook = (uu___249_17328.synth_hook);
        splice = (uu___249_17328.splice);
        is_native_tactic = (uu___249_17328.is_native_tactic);
        identifier_info = (uu___249_17328.identifier_info);
        tc_hooks = (uu___249_17328.tc_hooks);
        dsenv = (uu___249_17328.dsenv);
        dep_graph = (uu___249_17328.dep_graph)
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
            (let uu___250_17383 = env  in
             {
               solver = (uu___250_17383.solver);
               range = (uu___250_17383.range);
               curmodule = (uu___250_17383.curmodule);
               gamma = rest;
               gamma_sig = (uu___250_17383.gamma_sig);
               gamma_cache = (uu___250_17383.gamma_cache);
               modules = (uu___250_17383.modules);
               expected_typ = (uu___250_17383.expected_typ);
               sigtab = (uu___250_17383.sigtab);
               is_pattern = (uu___250_17383.is_pattern);
               instantiate_imp = (uu___250_17383.instantiate_imp);
               effects = (uu___250_17383.effects);
               generalize = (uu___250_17383.generalize);
               letrecs = (uu___250_17383.letrecs);
               top_level = (uu___250_17383.top_level);
               check_uvars = (uu___250_17383.check_uvars);
               use_eq = (uu___250_17383.use_eq);
               is_iface = (uu___250_17383.is_iface);
               admit = (uu___250_17383.admit);
               lax = (uu___250_17383.lax);
               lax_universes = (uu___250_17383.lax_universes);
               failhard = (uu___250_17383.failhard);
               nosynth = (uu___250_17383.nosynth);
               uvar_subtyping = (uu___250_17383.uvar_subtyping);
               tc_term = (uu___250_17383.tc_term);
               type_of = (uu___250_17383.type_of);
               universe_of = (uu___250_17383.universe_of);
               check_type_of = (uu___250_17383.check_type_of);
               use_bv_sorts = (uu___250_17383.use_bv_sorts);
               qtbl_name_and_index = (uu___250_17383.qtbl_name_and_index);
               normalized_eff_names = (uu___250_17383.normalized_eff_names);
               proof_ns = (uu___250_17383.proof_ns);
               synth_hook = (uu___250_17383.synth_hook);
               splice = (uu___250_17383.splice);
               is_native_tactic = (uu___250_17383.is_native_tactic);
               identifier_info = (uu___250_17383.identifier_info);
               tc_hooks = (uu___250_17383.tc_hooks);
               dsenv = (uu___250_17383.dsenv);
               dep_graph = (uu___250_17383.dep_graph)
             }))
    | uu____17384 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17410  ->
             match uu____17410 with | (x,uu____17416) -> push_bv env1 x) env
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
            let uu___251_17446 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___251_17446.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___251_17446.FStar_Syntax_Syntax.index);
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
      (let uu___252_17486 = env  in
       {
         solver = (uu___252_17486.solver);
         range = (uu___252_17486.range);
         curmodule = (uu___252_17486.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___252_17486.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___252_17486.sigtab);
         is_pattern = (uu___252_17486.is_pattern);
         instantiate_imp = (uu___252_17486.instantiate_imp);
         effects = (uu___252_17486.effects);
         generalize = (uu___252_17486.generalize);
         letrecs = (uu___252_17486.letrecs);
         top_level = (uu___252_17486.top_level);
         check_uvars = (uu___252_17486.check_uvars);
         use_eq = (uu___252_17486.use_eq);
         is_iface = (uu___252_17486.is_iface);
         admit = (uu___252_17486.admit);
         lax = (uu___252_17486.lax);
         lax_universes = (uu___252_17486.lax_universes);
         failhard = (uu___252_17486.failhard);
         nosynth = (uu___252_17486.nosynth);
         uvar_subtyping = (uu___252_17486.uvar_subtyping);
         tc_term = (uu___252_17486.tc_term);
         type_of = (uu___252_17486.type_of);
         universe_of = (uu___252_17486.universe_of);
         check_type_of = (uu___252_17486.check_type_of);
         use_bv_sorts = (uu___252_17486.use_bv_sorts);
         qtbl_name_and_index = (uu___252_17486.qtbl_name_and_index);
         normalized_eff_names = (uu___252_17486.normalized_eff_names);
         proof_ns = (uu___252_17486.proof_ns);
         synth_hook = (uu___252_17486.synth_hook);
         splice = (uu___252_17486.splice);
         is_native_tactic = (uu___252_17486.is_native_tactic);
         identifier_info = (uu___252_17486.identifier_info);
         tc_hooks = (uu___252_17486.tc_hooks);
         dsenv = (uu___252_17486.dsenv);
         dep_graph = (uu___252_17486.dep_graph)
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
        let uu____17528 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17528 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17556 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17556)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___253_17571 = env  in
      {
        solver = (uu___253_17571.solver);
        range = (uu___253_17571.range);
        curmodule = (uu___253_17571.curmodule);
        gamma = (uu___253_17571.gamma);
        gamma_sig = (uu___253_17571.gamma_sig);
        gamma_cache = (uu___253_17571.gamma_cache);
        modules = (uu___253_17571.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___253_17571.sigtab);
        is_pattern = (uu___253_17571.is_pattern);
        instantiate_imp = (uu___253_17571.instantiate_imp);
        effects = (uu___253_17571.effects);
        generalize = (uu___253_17571.generalize);
        letrecs = (uu___253_17571.letrecs);
        top_level = (uu___253_17571.top_level);
        check_uvars = (uu___253_17571.check_uvars);
        use_eq = false;
        is_iface = (uu___253_17571.is_iface);
        admit = (uu___253_17571.admit);
        lax = (uu___253_17571.lax);
        lax_universes = (uu___253_17571.lax_universes);
        failhard = (uu___253_17571.failhard);
        nosynth = (uu___253_17571.nosynth);
        uvar_subtyping = (uu___253_17571.uvar_subtyping);
        tc_term = (uu___253_17571.tc_term);
        type_of = (uu___253_17571.type_of);
        universe_of = (uu___253_17571.universe_of);
        check_type_of = (uu___253_17571.check_type_of);
        use_bv_sorts = (uu___253_17571.use_bv_sorts);
        qtbl_name_and_index = (uu___253_17571.qtbl_name_and_index);
        normalized_eff_names = (uu___253_17571.normalized_eff_names);
        proof_ns = (uu___253_17571.proof_ns);
        synth_hook = (uu___253_17571.synth_hook);
        splice = (uu___253_17571.splice);
        is_native_tactic = (uu___253_17571.is_native_tactic);
        identifier_info = (uu___253_17571.identifier_info);
        tc_hooks = (uu___253_17571.tc_hooks);
        dsenv = (uu___253_17571.dsenv);
        dep_graph = (uu___253_17571.dep_graph)
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
    let uu____17599 = expected_typ env_  in
    ((let uu___254_17605 = env_  in
      {
        solver = (uu___254_17605.solver);
        range = (uu___254_17605.range);
        curmodule = (uu___254_17605.curmodule);
        gamma = (uu___254_17605.gamma);
        gamma_sig = (uu___254_17605.gamma_sig);
        gamma_cache = (uu___254_17605.gamma_cache);
        modules = (uu___254_17605.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___254_17605.sigtab);
        is_pattern = (uu___254_17605.is_pattern);
        instantiate_imp = (uu___254_17605.instantiate_imp);
        effects = (uu___254_17605.effects);
        generalize = (uu___254_17605.generalize);
        letrecs = (uu___254_17605.letrecs);
        top_level = (uu___254_17605.top_level);
        check_uvars = (uu___254_17605.check_uvars);
        use_eq = false;
        is_iface = (uu___254_17605.is_iface);
        admit = (uu___254_17605.admit);
        lax = (uu___254_17605.lax);
        lax_universes = (uu___254_17605.lax_universes);
        failhard = (uu___254_17605.failhard);
        nosynth = (uu___254_17605.nosynth);
        uvar_subtyping = (uu___254_17605.uvar_subtyping);
        tc_term = (uu___254_17605.tc_term);
        type_of = (uu___254_17605.type_of);
        universe_of = (uu___254_17605.universe_of);
        check_type_of = (uu___254_17605.check_type_of);
        use_bv_sorts = (uu___254_17605.use_bv_sorts);
        qtbl_name_and_index = (uu___254_17605.qtbl_name_and_index);
        normalized_eff_names = (uu___254_17605.normalized_eff_names);
        proof_ns = (uu___254_17605.proof_ns);
        synth_hook = (uu___254_17605.synth_hook);
        splice = (uu___254_17605.splice);
        is_native_tactic = (uu___254_17605.is_native_tactic);
        identifier_info = (uu___254_17605.identifier_info);
        tc_hooks = (uu___254_17605.tc_hooks);
        dsenv = (uu___254_17605.dsenv);
        dep_graph = (uu___254_17605.dep_graph)
      }), uu____17599)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17615 =
      let uu____17618 = FStar_Ident.id_of_text ""  in [uu____17618]  in
    FStar_Ident.lid_of_ids uu____17615  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17624 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17624
        then
          let uu____17627 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17627 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___255_17654 = env  in
       {
         solver = (uu___255_17654.solver);
         range = (uu___255_17654.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___255_17654.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___255_17654.expected_typ);
         sigtab = (uu___255_17654.sigtab);
         is_pattern = (uu___255_17654.is_pattern);
         instantiate_imp = (uu___255_17654.instantiate_imp);
         effects = (uu___255_17654.effects);
         generalize = (uu___255_17654.generalize);
         letrecs = (uu___255_17654.letrecs);
         top_level = (uu___255_17654.top_level);
         check_uvars = (uu___255_17654.check_uvars);
         use_eq = (uu___255_17654.use_eq);
         is_iface = (uu___255_17654.is_iface);
         admit = (uu___255_17654.admit);
         lax = (uu___255_17654.lax);
         lax_universes = (uu___255_17654.lax_universes);
         failhard = (uu___255_17654.failhard);
         nosynth = (uu___255_17654.nosynth);
         uvar_subtyping = (uu___255_17654.uvar_subtyping);
         tc_term = (uu___255_17654.tc_term);
         type_of = (uu___255_17654.type_of);
         universe_of = (uu___255_17654.universe_of);
         check_type_of = (uu___255_17654.check_type_of);
         use_bv_sorts = (uu___255_17654.use_bv_sorts);
         qtbl_name_and_index = (uu___255_17654.qtbl_name_and_index);
         normalized_eff_names = (uu___255_17654.normalized_eff_names);
         proof_ns = (uu___255_17654.proof_ns);
         synth_hook = (uu___255_17654.synth_hook);
         splice = (uu___255_17654.splice);
         is_native_tactic = (uu___255_17654.is_native_tactic);
         identifier_info = (uu___255_17654.identifier_info);
         tc_hooks = (uu___255_17654.tc_hooks);
         dsenv = (uu___255_17654.dsenv);
         dep_graph = (uu___255_17654.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17705)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17709,(uu____17710,t)))::tl1
          ->
          let uu____17731 =
            let uu____17734 = FStar_Syntax_Free.uvars t  in
            ext out uu____17734  in
          aux uu____17731 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17737;
            FStar_Syntax_Syntax.index = uu____17738;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17745 =
            let uu____17748 = FStar_Syntax_Free.uvars t  in
            ext out uu____17748  in
          aux uu____17745 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17805)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17809,(uu____17810,t)))::tl1
          ->
          let uu____17831 =
            let uu____17834 = FStar_Syntax_Free.univs t  in
            ext out uu____17834  in
          aux uu____17831 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17837;
            FStar_Syntax_Syntax.index = uu____17838;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17845 =
            let uu____17848 = FStar_Syntax_Free.univs t  in
            ext out uu____17848  in
          aux uu____17845 tl1
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
          let uu____17909 = FStar_Util.set_add uname out  in
          aux uu____17909 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17912,(uu____17913,t)))::tl1
          ->
          let uu____17934 =
            let uu____17937 = FStar_Syntax_Free.univnames t  in
            ext out uu____17937  in
          aux uu____17934 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17940;
            FStar_Syntax_Syntax.index = uu____17941;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17948 =
            let uu____17951 = FStar_Syntax_Free.univnames t  in
            ext out uu____17951  in
          aux uu____17948 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___229_17971  ->
            match uu___229_17971 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____17975 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____17988 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____17998 =
      let uu____18005 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____18005
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____17998 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____18043 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___230_18053  ->
              match uu___230_18053 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____18055 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____18055
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____18058) ->
                  let uu____18075 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____18075))
       in
    FStar_All.pipe_right uu____18043 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___231_18082  ->
    match uu___231_18082 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____18084 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____18084
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18104  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18146) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18165,uu____18166) -> false  in
      let uu____18175 =
        FStar_List.tryFind
          (fun uu____18193  ->
             match uu____18193 with | (p,uu____18201) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18175 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18212,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18234 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18234
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___256_18252 = e  in
        {
          solver = (uu___256_18252.solver);
          range = (uu___256_18252.range);
          curmodule = (uu___256_18252.curmodule);
          gamma = (uu___256_18252.gamma);
          gamma_sig = (uu___256_18252.gamma_sig);
          gamma_cache = (uu___256_18252.gamma_cache);
          modules = (uu___256_18252.modules);
          expected_typ = (uu___256_18252.expected_typ);
          sigtab = (uu___256_18252.sigtab);
          is_pattern = (uu___256_18252.is_pattern);
          instantiate_imp = (uu___256_18252.instantiate_imp);
          effects = (uu___256_18252.effects);
          generalize = (uu___256_18252.generalize);
          letrecs = (uu___256_18252.letrecs);
          top_level = (uu___256_18252.top_level);
          check_uvars = (uu___256_18252.check_uvars);
          use_eq = (uu___256_18252.use_eq);
          is_iface = (uu___256_18252.is_iface);
          admit = (uu___256_18252.admit);
          lax = (uu___256_18252.lax);
          lax_universes = (uu___256_18252.lax_universes);
          failhard = (uu___256_18252.failhard);
          nosynth = (uu___256_18252.nosynth);
          uvar_subtyping = (uu___256_18252.uvar_subtyping);
          tc_term = (uu___256_18252.tc_term);
          type_of = (uu___256_18252.type_of);
          universe_of = (uu___256_18252.universe_of);
          check_type_of = (uu___256_18252.check_type_of);
          use_bv_sorts = (uu___256_18252.use_bv_sorts);
          qtbl_name_and_index = (uu___256_18252.qtbl_name_and_index);
          normalized_eff_names = (uu___256_18252.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___256_18252.synth_hook);
          splice = (uu___256_18252.splice);
          is_native_tactic = (uu___256_18252.is_native_tactic);
          identifier_info = (uu___256_18252.identifier_info);
          tc_hooks = (uu___256_18252.tc_hooks);
          dsenv = (uu___256_18252.dsenv);
          dep_graph = (uu___256_18252.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___257_18292 = e  in
      {
        solver = (uu___257_18292.solver);
        range = (uu___257_18292.range);
        curmodule = (uu___257_18292.curmodule);
        gamma = (uu___257_18292.gamma);
        gamma_sig = (uu___257_18292.gamma_sig);
        gamma_cache = (uu___257_18292.gamma_cache);
        modules = (uu___257_18292.modules);
        expected_typ = (uu___257_18292.expected_typ);
        sigtab = (uu___257_18292.sigtab);
        is_pattern = (uu___257_18292.is_pattern);
        instantiate_imp = (uu___257_18292.instantiate_imp);
        effects = (uu___257_18292.effects);
        generalize = (uu___257_18292.generalize);
        letrecs = (uu___257_18292.letrecs);
        top_level = (uu___257_18292.top_level);
        check_uvars = (uu___257_18292.check_uvars);
        use_eq = (uu___257_18292.use_eq);
        is_iface = (uu___257_18292.is_iface);
        admit = (uu___257_18292.admit);
        lax = (uu___257_18292.lax);
        lax_universes = (uu___257_18292.lax_universes);
        failhard = (uu___257_18292.failhard);
        nosynth = (uu___257_18292.nosynth);
        uvar_subtyping = (uu___257_18292.uvar_subtyping);
        tc_term = (uu___257_18292.tc_term);
        type_of = (uu___257_18292.type_of);
        universe_of = (uu___257_18292.universe_of);
        check_type_of = (uu___257_18292.check_type_of);
        use_bv_sorts = (uu___257_18292.use_bv_sorts);
        qtbl_name_and_index = (uu___257_18292.qtbl_name_and_index);
        normalized_eff_names = (uu___257_18292.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___257_18292.synth_hook);
        splice = (uu___257_18292.splice);
        is_native_tactic = (uu___257_18292.is_native_tactic);
        identifier_info = (uu___257_18292.identifier_info);
        tc_hooks = (uu___257_18292.tc_hooks);
        dsenv = (uu___257_18292.dsenv);
        dep_graph = (uu___257_18292.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18307 = FStar_Syntax_Free.names t  in
      let uu____18310 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18307 uu____18310
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18331 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18331
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18339 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18339
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18356 =
      match uu____18356 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18366 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18366)
       in
    let uu____18368 =
      let uu____18371 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18371 FStar_List.rev  in
    FStar_All.pipe_right uu____18368 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18386  -> ());
    push = (fun uu____18388  -> ());
    pop = (fun uu____18390  -> ());
    snapshot =
      (fun uu____18392  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18401  -> fun uu____18402  -> ());
    encode_modul = (fun uu____18413  -> fun uu____18414  -> ());
    encode_sig = (fun uu____18417  -> fun uu____18418  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18424 =
             let uu____18431 = FStar_Options.peek ()  in (e, g, uu____18431)
              in
           [uu____18424]);
    solve = (fun uu____18447  -> fun uu____18448  -> fun uu____18449  -> ());
    finish = (fun uu____18455  -> ());
    refresh = (fun uu____18457  -> ())
  } 