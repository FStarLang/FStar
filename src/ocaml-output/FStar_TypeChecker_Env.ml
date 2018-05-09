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
    FStar_Pervasives_Native.tuple4[@@deriving show]
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
                             ((let uu____9865 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9865
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9876 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9876
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9903,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9935 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9961  ->
                  match uu____9961 with
                  | (m,uu____9967) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9935 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___116_9975 = env  in
               {
                 solver = (uu___116_9975.solver);
                 range = (uu___116_9975.range);
                 curmodule = (uu___116_9975.curmodule);
                 gamma = (uu___116_9975.gamma);
                 gamma_sig = (uu___116_9975.gamma_sig);
                 gamma_cache = (uu___116_9975.gamma_cache);
                 modules = (uu___116_9975.modules);
                 expected_typ = (uu___116_9975.expected_typ);
                 sigtab = (uu___116_9975.sigtab);
                 is_pattern = (uu___116_9975.is_pattern);
                 instantiate_imp = (uu___116_9975.instantiate_imp);
                 effects = (uu___116_9975.effects);
                 generalize = (uu___116_9975.generalize);
                 letrecs = (uu___116_9975.letrecs);
                 top_level = (uu___116_9975.top_level);
                 check_uvars = (uu___116_9975.check_uvars);
                 use_eq = (uu___116_9975.use_eq);
                 is_iface = (uu___116_9975.is_iface);
                 admit = (uu___116_9975.admit);
                 lax = (uu___116_9975.lax);
                 lax_universes = (uu___116_9975.lax_universes);
                 failhard = (uu___116_9975.failhard);
                 nosynth = (uu___116_9975.nosynth);
                 uvar_subtyping = (uu___116_9975.uvar_subtyping);
                 tc_term = (uu___116_9975.tc_term);
                 type_of = (uu___116_9975.type_of);
                 universe_of = (uu___116_9975.universe_of);
                 check_type_of = (uu___116_9975.check_type_of);
                 use_bv_sorts = (uu___116_9975.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___116_9975.normalized_eff_names);
                 proof_ns = (uu___116_9975.proof_ns);
                 synth_hook = (uu___116_9975.synth_hook);
                 splice = (uu___116_9975.splice);
                 is_native_tactic = (uu___116_9975.is_native_tactic);
                 identifier_info = (uu___116_9975.identifier_info);
                 tc_hooks = (uu___116_9975.tc_hooks);
                 dsenv = (uu___116_9975.dsenv);
                 dep_graph = (uu___116_9975.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9988,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___117_9997 = env  in
               {
                 solver = (uu___117_9997.solver);
                 range = (uu___117_9997.range);
                 curmodule = (uu___117_9997.curmodule);
                 gamma = (uu___117_9997.gamma);
                 gamma_sig = (uu___117_9997.gamma_sig);
                 gamma_cache = (uu___117_9997.gamma_cache);
                 modules = (uu___117_9997.modules);
                 expected_typ = (uu___117_9997.expected_typ);
                 sigtab = (uu___117_9997.sigtab);
                 is_pattern = (uu___117_9997.is_pattern);
                 instantiate_imp = (uu___117_9997.instantiate_imp);
                 effects = (uu___117_9997.effects);
                 generalize = (uu___117_9997.generalize);
                 letrecs = (uu___117_9997.letrecs);
                 top_level = (uu___117_9997.top_level);
                 check_uvars = (uu___117_9997.check_uvars);
                 use_eq = (uu___117_9997.use_eq);
                 is_iface = (uu___117_9997.is_iface);
                 admit = (uu___117_9997.admit);
                 lax = (uu___117_9997.lax);
                 lax_universes = (uu___117_9997.lax_universes);
                 failhard = (uu___117_9997.failhard);
                 nosynth = (uu___117_9997.nosynth);
                 uvar_subtyping = (uu___117_9997.uvar_subtyping);
                 tc_term = (uu___117_9997.tc_term);
                 type_of = (uu___117_9997.type_of);
                 universe_of = (uu___117_9997.universe_of);
                 check_type_of = (uu___117_9997.check_type_of);
                 use_bv_sorts = (uu___117_9997.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___117_9997.normalized_eff_names);
                 proof_ns = (uu___117_9997.proof_ns);
                 synth_hook = (uu___117_9997.synth_hook);
                 splice = (uu___117_9997.splice);
                 is_native_tactic = (uu___117_9997.is_native_tactic);
                 identifier_info = (uu___117_9997.identifier_info);
                 tc_hooks = (uu___117_9997.tc_hooks);
                 dsenv = (uu___117_9997.dsenv);
                 dep_graph = (uu___117_9997.dep_graph)
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
        (let uu___118_10031 = e  in
         {
           solver = (uu___118_10031.solver);
           range = r;
           curmodule = (uu___118_10031.curmodule);
           gamma = (uu___118_10031.gamma);
           gamma_sig = (uu___118_10031.gamma_sig);
           gamma_cache = (uu___118_10031.gamma_cache);
           modules = (uu___118_10031.modules);
           expected_typ = (uu___118_10031.expected_typ);
           sigtab = (uu___118_10031.sigtab);
           is_pattern = (uu___118_10031.is_pattern);
           instantiate_imp = (uu___118_10031.instantiate_imp);
           effects = (uu___118_10031.effects);
           generalize = (uu___118_10031.generalize);
           letrecs = (uu___118_10031.letrecs);
           top_level = (uu___118_10031.top_level);
           check_uvars = (uu___118_10031.check_uvars);
           use_eq = (uu___118_10031.use_eq);
           is_iface = (uu___118_10031.is_iface);
           admit = (uu___118_10031.admit);
           lax = (uu___118_10031.lax);
           lax_universes = (uu___118_10031.lax_universes);
           failhard = (uu___118_10031.failhard);
           nosynth = (uu___118_10031.nosynth);
           uvar_subtyping = (uu___118_10031.uvar_subtyping);
           tc_term = (uu___118_10031.tc_term);
           type_of = (uu___118_10031.type_of);
           universe_of = (uu___118_10031.universe_of);
           check_type_of = (uu___118_10031.check_type_of);
           use_bv_sorts = (uu___118_10031.use_bv_sorts);
           qtbl_name_and_index = (uu___118_10031.qtbl_name_and_index);
           normalized_eff_names = (uu___118_10031.normalized_eff_names);
           proof_ns = (uu___118_10031.proof_ns);
           synth_hook = (uu___118_10031.synth_hook);
           splice = (uu___118_10031.splice);
           is_native_tactic = (uu___118_10031.is_native_tactic);
           identifier_info = (uu___118_10031.identifier_info);
           tc_hooks = (uu___118_10031.tc_hooks);
           dsenv = (uu___118_10031.dsenv);
           dep_graph = (uu___118_10031.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____10047 =
        let uu____10048 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____10048 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10047
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____10110 =
          let uu____10111 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____10111 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10110
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____10173 =
          let uu____10174 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____10174 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____10173
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____10236 =
        let uu____10237 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10237 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____10236
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___119_10306 = env  in
      {
        solver = (uu___119_10306.solver);
        range = (uu___119_10306.range);
        curmodule = lid;
        gamma = (uu___119_10306.gamma);
        gamma_sig = (uu___119_10306.gamma_sig);
        gamma_cache = (uu___119_10306.gamma_cache);
        modules = (uu___119_10306.modules);
        expected_typ = (uu___119_10306.expected_typ);
        sigtab = (uu___119_10306.sigtab);
        is_pattern = (uu___119_10306.is_pattern);
        instantiate_imp = (uu___119_10306.instantiate_imp);
        effects = (uu___119_10306.effects);
        generalize = (uu___119_10306.generalize);
        letrecs = (uu___119_10306.letrecs);
        top_level = (uu___119_10306.top_level);
        check_uvars = (uu___119_10306.check_uvars);
        use_eq = (uu___119_10306.use_eq);
        is_iface = (uu___119_10306.is_iface);
        admit = (uu___119_10306.admit);
        lax = (uu___119_10306.lax);
        lax_universes = (uu___119_10306.lax_universes);
        failhard = (uu___119_10306.failhard);
        nosynth = (uu___119_10306.nosynth);
        uvar_subtyping = (uu___119_10306.uvar_subtyping);
        tc_term = (uu___119_10306.tc_term);
        type_of = (uu___119_10306.type_of);
        universe_of = (uu___119_10306.universe_of);
        check_type_of = (uu___119_10306.check_type_of);
        use_bv_sorts = (uu___119_10306.use_bv_sorts);
        qtbl_name_and_index = (uu___119_10306.qtbl_name_and_index);
        normalized_eff_names = (uu___119_10306.normalized_eff_names);
        proof_ns = (uu___119_10306.proof_ns);
        synth_hook = (uu___119_10306.synth_hook);
        splice = (uu___119_10306.splice);
        is_native_tactic = (uu___119_10306.is_native_tactic);
        identifier_info = (uu___119_10306.identifier_info);
        tc_hooks = (uu___119_10306.tc_hooks);
        dsenv = (uu___119_10306.dsenv);
        dep_graph = (uu___119_10306.dep_graph)
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
      let uu____10333 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10333
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10343 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10343)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10353 =
      let uu____10354 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10354  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10353)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10359  ->
    let uu____10360 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10360
  
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
      | ((formals,t),uu____10416) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10450 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10450)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___97_10466  ->
    match uu___97_10466 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10492  -> new_u_univ ()))
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
      let uu____10511 = inst_tscheme t  in
      match uu____10511 with
      | (us,t1) ->
          let uu____10522 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10522)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10542  ->
          match uu____10542 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10561 =
                         let uu____10562 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10563 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10564 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10565 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10562 uu____10563 uu____10564 uu____10565
                          in
                       failwith uu____10561)
                    else ();
                    (let uu____10567 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10567))
               | uu____10576 ->
                   let uu____10577 =
                     let uu____10578 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10578
                      in
                   failwith uu____10577)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10584 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10590 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10596 -> false
  
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
             | ([],uu____10638) -> Maybe
             | (uu____10645,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10664 -> No  in
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
          let uu____10755 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10755 with
          | FStar_Pervasives_Native.None  ->
              let uu____10778 =
                FStar_Util.find_map env.gamma
                  (fun uu___98_10822  ->
                     match uu___98_10822 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____10861 = FStar_Ident.lid_equals lid l  in
                         if uu____10861
                         then
                           let uu____10882 =
                             let uu____10901 =
                               let uu____10916 = inst_tscheme t  in
                               FStar_Util.Inl uu____10916  in
                             let uu____10931 = FStar_Ident.range_of_lid l  in
                             (uu____10901, uu____10931)  in
                           FStar_Pervasives_Native.Some uu____10882
                         else FStar_Pervasives_Native.None
                     | uu____10983 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____10778
                (fun uu____11021  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___99_11030  ->
                        match uu___99_11030 with
                        | (uu____11033,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____11035);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____11036;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____11037;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____11038;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____11039;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____11059 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____11059
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
                                  uu____11107 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____11114 -> cache t  in
                            let uu____11115 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____11115 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____11121 =
                                   let uu____11122 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____11122)
                                    in
                                 maybe_cache uu____11121)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____11190 = find_in_sigtab env lid  in
         match uu____11190 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11277) ->
          add_sigelts env ses
      | uu____11286 ->
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
            | uu____11300 -> ()))

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
        (fun uu___100_11331  ->
           match uu___100_11331 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11349 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11410,lb::[]),uu____11412) ->
            let uu____11419 =
              let uu____11428 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11437 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11428, uu____11437)  in
            FStar_Pervasives_Native.Some uu____11419
        | FStar_Syntax_Syntax.Sig_let ((uu____11450,lbs),uu____11452) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11482 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11494 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11494
                     then
                       let uu____11505 =
                         let uu____11514 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11523 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11514, uu____11523)  in
                       FStar_Pervasives_Native.Some uu____11505
                     else FStar_Pervasives_Native.None)
        | uu____11545 -> FStar_Pervasives_Native.None
  
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
          let uu____11604 =
            let uu____11613 =
              let uu____11618 =
                let uu____11619 =
                  let uu____11622 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11622
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11619)  in
              inst_tscheme1 uu____11618  in
            (uu____11613, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11604
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11644,uu____11645) ->
          let uu____11650 =
            let uu____11659 =
              let uu____11664 =
                let uu____11665 =
                  let uu____11668 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11668  in
                (us, uu____11665)  in
              inst_tscheme1 uu____11664  in
            (uu____11659, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11650
      | uu____11687 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11775 =
          match uu____11775 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11871,uvs,t,uu____11874,uu____11875,uu____11876);
                      FStar_Syntax_Syntax.sigrng = uu____11877;
                      FStar_Syntax_Syntax.sigquals = uu____11878;
                      FStar_Syntax_Syntax.sigmeta = uu____11879;
                      FStar_Syntax_Syntax.sigattrs = uu____11880;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11901 =
                     let uu____11910 = inst_tscheme1 (uvs, t)  in
                     (uu____11910, rng)  in
                   FStar_Pervasives_Native.Some uu____11901
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11934;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11936;
                      FStar_Syntax_Syntax.sigattrs = uu____11937;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11954 =
                     let uu____11955 = in_cur_mod env l  in uu____11955 = Yes
                      in
                   if uu____11954
                   then
                     let uu____11966 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____11966
                      then
                        let uu____11979 =
                          let uu____11988 = inst_tscheme1 (uvs, t)  in
                          (uu____11988, rng)  in
                        FStar_Pervasives_Native.Some uu____11979
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____12019 =
                        let uu____12028 = inst_tscheme1 (uvs, t)  in
                        (uu____12028, rng)  in
                      FStar_Pervasives_Native.Some uu____12019)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12053,uu____12054);
                      FStar_Syntax_Syntax.sigrng = uu____12055;
                      FStar_Syntax_Syntax.sigquals = uu____12056;
                      FStar_Syntax_Syntax.sigmeta = uu____12057;
                      FStar_Syntax_Syntax.sigattrs = uu____12058;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____12097 =
                          let uu____12106 = inst_tscheme1 (uvs, k)  in
                          (uu____12106, rng)  in
                        FStar_Pervasives_Native.Some uu____12097
                    | uu____12127 ->
                        let uu____12128 =
                          let uu____12137 =
                            let uu____12142 =
                              let uu____12143 =
                                let uu____12146 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12146
                                 in
                              (uvs, uu____12143)  in
                            inst_tscheme1 uu____12142  in
                          (uu____12137, rng)  in
                        FStar_Pervasives_Native.Some uu____12128)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____12169,uu____12170);
                      FStar_Syntax_Syntax.sigrng = uu____12171;
                      FStar_Syntax_Syntax.sigquals = uu____12172;
                      FStar_Syntax_Syntax.sigmeta = uu____12173;
                      FStar_Syntax_Syntax.sigattrs = uu____12174;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12214 =
                          let uu____12223 = inst_tscheme_with (uvs, k) us  in
                          (uu____12223, rng)  in
                        FStar_Pervasives_Native.Some uu____12214
                    | uu____12244 ->
                        let uu____12245 =
                          let uu____12254 =
                            let uu____12259 =
                              let uu____12260 =
                                let uu____12263 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12263
                                 in
                              (uvs, uu____12260)  in
                            inst_tscheme_with uu____12259 us  in
                          (uu____12254, rng)  in
                        FStar_Pervasives_Native.Some uu____12245)
               | FStar_Util.Inr se ->
                   let uu____12299 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12320;
                          FStar_Syntax_Syntax.sigrng = uu____12321;
                          FStar_Syntax_Syntax.sigquals = uu____12322;
                          FStar_Syntax_Syntax.sigmeta = uu____12323;
                          FStar_Syntax_Syntax.sigattrs = uu____12324;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12339 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12299
                     (FStar_Util.map_option
                        (fun uu____12387  ->
                           match uu____12387 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12418 =
          let uu____12429 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12429 mapper  in
        match uu____12418 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12503 =
              let uu____12514 =
                let uu____12521 =
                  let uu___120_12524 = t  in
                  let uu____12525 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___120_12524.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12525;
                    FStar_Syntax_Syntax.vars =
                      (uu___120_12524.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12521)  in
              (uu____12514, r)  in
            FStar_Pervasives_Native.Some uu____12503
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12572 = lookup_qname env l  in
      match uu____12572 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12591 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12643 = try_lookup_bv env bv  in
      match uu____12643 with
      | FStar_Pervasives_Native.None  ->
          let uu____12658 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12658 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12673 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12674 =
            let uu____12675 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12675  in
          (uu____12673, uu____12674)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12696 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12696 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12762 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12762  in
          let uu____12763 =
            let uu____12772 =
              let uu____12777 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12777)  in
            (uu____12772, r1)  in
          FStar_Pervasives_Native.Some uu____12763
  
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
        let uu____12811 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12811 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12844,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12869 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12869  in
            let uu____12870 =
              let uu____12875 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12875, r1)  in
            FStar_Pervasives_Native.Some uu____12870
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12898 = try_lookup_lid env l  in
      match uu____12898 with
      | FStar_Pervasives_Native.None  ->
          let uu____12925 = name_not_found l  in
          let uu____12930 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12925 uu____12930
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_12970  ->
              match uu___101_12970 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12972 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12991 = lookup_qname env lid  in
      match uu____12991 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13000,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13003;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13005;
              FStar_Syntax_Syntax.sigattrs = uu____13006;_},FStar_Pervasives_Native.None
            ),uu____13007)
          ->
          let uu____13056 =
            let uu____13063 =
              let uu____13064 =
                let uu____13067 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____13067 t  in
              (uvs, uu____13064)  in
            (uu____13063, q)  in
          FStar_Pervasives_Native.Some uu____13056
      | uu____13080 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13101 = lookup_qname env lid  in
      match uu____13101 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13106,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13109;
              FStar_Syntax_Syntax.sigquals = uu____13110;
              FStar_Syntax_Syntax.sigmeta = uu____13111;
              FStar_Syntax_Syntax.sigattrs = uu____13112;_},FStar_Pervasives_Native.None
            ),uu____13113)
          ->
          let uu____13162 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13162 (uvs, t)
      | uu____13167 ->
          let uu____13168 = name_not_found lid  in
          let uu____13173 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13168 uu____13173
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13192 = lookup_qname env lid  in
      match uu____13192 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13197,uvs,t,uu____13200,uu____13201,uu____13202);
              FStar_Syntax_Syntax.sigrng = uu____13203;
              FStar_Syntax_Syntax.sigquals = uu____13204;
              FStar_Syntax_Syntax.sigmeta = uu____13205;
              FStar_Syntax_Syntax.sigattrs = uu____13206;_},FStar_Pervasives_Native.None
            ),uu____13207)
          ->
          let uu____13260 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13260 (uvs, t)
      | uu____13265 ->
          let uu____13266 = name_not_found lid  in
          let uu____13271 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13266 uu____13271
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13292 = lookup_qname env lid  in
      match uu____13292 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13299,uu____13300,uu____13301,uu____13302,uu____13303,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13305;
              FStar_Syntax_Syntax.sigquals = uu____13306;
              FStar_Syntax_Syntax.sigmeta = uu____13307;
              FStar_Syntax_Syntax.sigattrs = uu____13308;_},uu____13309),uu____13310)
          -> (true, dcs)
      | uu____13371 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13384 = lookup_qname env lid  in
      match uu____13384 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13385,uu____13386,uu____13387,l,uu____13389,uu____13390);
              FStar_Syntax_Syntax.sigrng = uu____13391;
              FStar_Syntax_Syntax.sigquals = uu____13392;
              FStar_Syntax_Syntax.sigmeta = uu____13393;
              FStar_Syntax_Syntax.sigattrs = uu____13394;_},uu____13395),uu____13396)
          -> l
      | uu____13451 ->
          let uu____13452 =
            let uu____13453 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13453  in
          failwith uu____13452
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13502)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13553,lbs),uu____13555)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13577 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13577
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13609 -> FStar_Pervasives_Native.None)
        | uu____13614 -> FStar_Pervasives_Native.None
  
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
        let uu____13644 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13644
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13669),uu____13670) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13719 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13740 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13740
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13759 = lookup_qname env ftv  in
      match uu____13759 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13763) ->
          let uu____13808 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13808 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13829,t),r) ->
               let uu____13844 =
                 let uu____13845 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13845 t  in
               FStar_Pervasives_Native.Some uu____13844)
      | uu____13846 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13857 = try_lookup_effect_lid env ftv  in
      match uu____13857 with
      | FStar_Pervasives_Native.None  ->
          let uu____13860 = name_not_found ftv  in
          let uu____13865 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13860 uu____13865
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
        let uu____13888 = lookup_qname env lid0  in
        match uu____13888 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13899);
                FStar_Syntax_Syntax.sigrng = uu____13900;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13902;
                FStar_Syntax_Syntax.sigattrs = uu____13903;_},FStar_Pervasives_Native.None
              ),uu____13904)
            ->
            let lid1 =
              let uu____13958 =
                let uu____13959 = FStar_Ident.range_of_lid lid  in
                let uu____13960 =
                  let uu____13961 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____13961  in
                FStar_Range.set_use_range uu____13959 uu____13960  in
              FStar_Ident.set_lid_range lid uu____13958  in
            let uu____13962 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_13966  ->
                      match uu___102_13966 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13967 -> false))
               in
            if uu____13962
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13981 =
                      let uu____13982 =
                        let uu____13983 = get_range env  in
                        FStar_Range.string_of_range uu____13983  in
                      let uu____13984 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____13985 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13982 uu____13984 uu____13985
                       in
                    failwith uu____13981)
                  in
               match (binders, univs1) with
               | ([],uu____14000) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____14021,uu____14022::uu____14023::uu____14024) ->
                   let uu____14041 =
                     let uu____14042 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____14043 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____14042 uu____14043
                      in
                   failwith uu____14041
               | uu____14050 ->
                   let uu____14063 =
                     let uu____14068 =
                       let uu____14069 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____14069)  in
                     inst_tscheme_with uu____14068 insts  in
                   (match uu____14063 with
                    | (uu____14082,t) ->
                        let t1 =
                          let uu____14085 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____14085 t  in
                        let uu____14086 =
                          let uu____14087 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14087.FStar_Syntax_Syntax.n  in
                        (match uu____14086 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____14118 -> failwith "Impossible")))
        | uu____14125 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____14148 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____14148 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____14161,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____14168 = find1 l2  in
            (match uu____14168 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____14175 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____14175 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____14179 = find1 l  in
            (match uu____14179 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____14184 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____14184
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____14198 = lookup_qname env l1  in
      match uu____14198 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____14201;
              FStar_Syntax_Syntax.sigrng = uu____14202;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14204;
              FStar_Syntax_Syntax.sigattrs = uu____14205;_},uu____14206),uu____14207)
          -> q
      | uu____14258 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14279 =
          let uu____14280 =
            let uu____14281 = FStar_Util.string_of_int i  in
            let uu____14282 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14281 uu____14282
             in
          failwith uu____14280  in
        let uu____14283 = lookup_datacon env lid  in
        match uu____14283 with
        | (uu____14288,t) ->
            let uu____14290 =
              let uu____14291 = FStar_Syntax_Subst.compress t  in
              uu____14291.FStar_Syntax_Syntax.n  in
            (match uu____14290 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14295) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14326 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14326
                      FStar_Pervasives_Native.fst)
             | uu____14335 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14346 = lookup_qname env l  in
      match uu____14346 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14347,uu____14348,uu____14349);
              FStar_Syntax_Syntax.sigrng = uu____14350;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14352;
              FStar_Syntax_Syntax.sigattrs = uu____14353;_},uu____14354),uu____14355)
          ->
          FStar_Util.for_some
            (fun uu___103_14408  ->
               match uu___103_14408 with
               | FStar_Syntax_Syntax.Projector uu____14409 -> true
               | uu____14414 -> false) quals
      | uu____14415 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14426 = lookup_qname env lid  in
      match uu____14426 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14427,uu____14428,uu____14429,uu____14430,uu____14431,uu____14432);
              FStar_Syntax_Syntax.sigrng = uu____14433;
              FStar_Syntax_Syntax.sigquals = uu____14434;
              FStar_Syntax_Syntax.sigmeta = uu____14435;
              FStar_Syntax_Syntax.sigattrs = uu____14436;_},uu____14437),uu____14438)
          -> true
      | uu____14493 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14504 = lookup_qname env lid  in
      match uu____14504 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14505,uu____14506,uu____14507,uu____14508,uu____14509,uu____14510);
              FStar_Syntax_Syntax.sigrng = uu____14511;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14513;
              FStar_Syntax_Syntax.sigattrs = uu____14514;_},uu____14515),uu____14516)
          ->
          FStar_Util.for_some
            (fun uu___104_14577  ->
               match uu___104_14577 with
               | FStar_Syntax_Syntax.RecordType uu____14578 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14587 -> true
               | uu____14596 -> false) quals
      | uu____14597 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14603,uu____14604);
            FStar_Syntax_Syntax.sigrng = uu____14605;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14607;
            FStar_Syntax_Syntax.sigattrs = uu____14608;_},uu____14609),uu____14610)
        ->
        FStar_Util.for_some
          (fun uu___105_14667  ->
             match uu___105_14667 with
             | FStar_Syntax_Syntax.Action uu____14668 -> true
             | uu____14669 -> false) quals
    | uu____14670 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14681 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14681
  
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
      let uu____14695 =
        let uu____14696 = FStar_Syntax_Util.un_uinst head1  in
        uu____14696.FStar_Syntax_Syntax.n  in
      match uu____14695 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14700 ->
               true
           | uu____14701 -> false)
      | uu____14702 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14713 = lookup_qname env l  in
      match uu____14713 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14715),uu____14716) ->
          FStar_Util.for_some
            (fun uu___106_14764  ->
               match uu___106_14764 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14765 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14766 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14837 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14853) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14870 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14877 ->
                 FStar_Pervasives_Native.Some true
             | uu____14894 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14895 =
        let uu____14898 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14898 mapper  in
      match uu____14895 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14948 = lookup_qname env lid  in
      match uu____14948 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14949,uu____14950,tps,uu____14952,uu____14953,uu____14954);
              FStar_Syntax_Syntax.sigrng = uu____14955;
              FStar_Syntax_Syntax.sigquals = uu____14956;
              FStar_Syntax_Syntax.sigmeta = uu____14957;
              FStar_Syntax_Syntax.sigattrs = uu____14958;_},uu____14959),uu____14960)
          -> FStar_List.length tps
      | uu____15023 ->
          let uu____15024 = name_not_found lid  in
          let uu____15029 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15024 uu____15029
  
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
           (fun uu____15073  ->
              match uu____15073 with
              | (d,uu____15081) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____15096 = effect_decl_opt env l  in
      match uu____15096 with
      | FStar_Pervasives_Native.None  ->
          let uu____15111 = name_not_found l  in
          let uu____15116 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15111 uu____15116
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____15138  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____15157  ->
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
        let uu____15188 = FStar_Ident.lid_equals l1 l2  in
        if uu____15188
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____15196 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____15196
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____15204 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15257  ->
                        match uu____15257 with
                        | (m1,m2,uu____15270,uu____15271,uu____15272) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____15204 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15289 =
                    let uu____15294 =
                      let uu____15295 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15296 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15295
                        uu____15296
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15294)
                     in
                  FStar_Errors.raise_error uu____15289 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15303,uu____15304,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15337 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15337
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
  'Auu____15353 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15353)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15382 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15408  ->
                match uu____15408 with
                | (d,uu____15414) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15382 with
      | FStar_Pervasives_Native.None  ->
          let uu____15425 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15425
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15438 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15438 with
           | (uu____15453,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15469)::(wp,uu____15471)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15507 -> failwith "Impossible"))
  
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
          let uu____15560 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15560
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15562 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15562
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
                  let uu____15570 = get_range env  in
                  let uu____15571 =
                    let uu____15578 =
                      let uu____15579 =
                        let uu____15594 =
                          let uu____15603 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15603]  in
                        (null_wp, uu____15594)  in
                      FStar_Syntax_Syntax.Tm_app uu____15579  in
                    FStar_Syntax_Syntax.mk uu____15578  in
                  uu____15571 FStar_Pervasives_Native.None uu____15570  in
                let uu____15635 =
                  let uu____15636 =
                    let uu____15645 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15645]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15636;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15635))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_15676 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_15676.order);
              joins = (uu___121_15676.joins)
            }  in
          let uu___122_15685 = env  in
          {
            solver = (uu___122_15685.solver);
            range = (uu___122_15685.range);
            curmodule = (uu___122_15685.curmodule);
            gamma = (uu___122_15685.gamma);
            gamma_sig = (uu___122_15685.gamma_sig);
            gamma_cache = (uu___122_15685.gamma_cache);
            modules = (uu___122_15685.modules);
            expected_typ = (uu___122_15685.expected_typ);
            sigtab = (uu___122_15685.sigtab);
            is_pattern = (uu___122_15685.is_pattern);
            instantiate_imp = (uu___122_15685.instantiate_imp);
            effects;
            generalize = (uu___122_15685.generalize);
            letrecs = (uu___122_15685.letrecs);
            top_level = (uu___122_15685.top_level);
            check_uvars = (uu___122_15685.check_uvars);
            use_eq = (uu___122_15685.use_eq);
            is_iface = (uu___122_15685.is_iface);
            admit = (uu___122_15685.admit);
            lax = (uu___122_15685.lax);
            lax_universes = (uu___122_15685.lax_universes);
            failhard = (uu___122_15685.failhard);
            nosynth = (uu___122_15685.nosynth);
            uvar_subtyping = (uu___122_15685.uvar_subtyping);
            tc_term = (uu___122_15685.tc_term);
            type_of = (uu___122_15685.type_of);
            universe_of = (uu___122_15685.universe_of);
            check_type_of = (uu___122_15685.check_type_of);
            use_bv_sorts = (uu___122_15685.use_bv_sorts);
            qtbl_name_and_index = (uu___122_15685.qtbl_name_and_index);
            normalized_eff_names = (uu___122_15685.normalized_eff_names);
            proof_ns = (uu___122_15685.proof_ns);
            synth_hook = (uu___122_15685.synth_hook);
            splice = (uu___122_15685.splice);
            is_native_tactic = (uu___122_15685.is_native_tactic);
            identifier_info = (uu___122_15685.identifier_info);
            tc_hooks = (uu___122_15685.tc_hooks);
            dsenv = (uu___122_15685.dsenv);
            dep_graph = (uu___122_15685.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15715 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15715  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15873 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15874 = l1 u t wp e  in
                                l2 u t uu____15873 uu____15874))
                | uu____15875 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15947 = inst_tscheme_with lift_t [u]  in
            match uu____15947 with
            | (uu____15954,lift_t1) ->
                let uu____15956 =
                  let uu____15963 =
                    let uu____15964 =
                      let uu____15979 =
                        let uu____15988 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15995 =
                          let uu____16004 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16004]  in
                        uu____15988 :: uu____15995  in
                      (lift_t1, uu____15979)  in
                    FStar_Syntax_Syntax.Tm_app uu____15964  in
                  FStar_Syntax_Syntax.mk uu____15963  in
                uu____15956 FStar_Pervasives_Native.None
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
            let uu____16106 = inst_tscheme_with lift_t [u]  in
            match uu____16106 with
            | (uu____16113,lift_t1) ->
                let uu____16115 =
                  let uu____16122 =
                    let uu____16123 =
                      let uu____16138 =
                        let uu____16147 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16154 =
                          let uu____16163 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____16170 =
                            let uu____16179 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16179]  in
                          uu____16163 :: uu____16170  in
                        uu____16147 :: uu____16154  in
                      (lift_t1, uu____16138)  in
                    FStar_Syntax_Syntax.Tm_app uu____16123  in
                  FStar_Syntax_Syntax.mk uu____16122  in
                uu____16115 FStar_Pervasives_Native.None
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
              let uu____16269 =
                let uu____16270 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____16270
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____16269  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____16274 =
              let uu____16275 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____16275  in
            let uu____16276 =
              let uu____16277 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____16303 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____16303)
                 in
              FStar_Util.dflt "none" uu____16277  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____16274
              uu____16276
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____16329  ->
                    match uu____16329 with
                    | (e,uu____16337) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____16360 =
            match uu____16360 with
            | (i,j) ->
                let uu____16371 = FStar_Ident.lid_equals i j  in
                if uu____16371
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
              let uu____16403 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16413 = FStar_Ident.lid_equals i k  in
                        if uu____16413
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16424 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16424
                                  then []
                                  else
                                    (let uu____16428 =
                                       let uu____16437 =
                                         find_edge order1 (i, k)  in
                                       let uu____16440 =
                                         find_edge order1 (k, j)  in
                                       (uu____16437, uu____16440)  in
                                     match uu____16428 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16455 =
                                           compose_edges e1 e2  in
                                         [uu____16455]
                                     | uu____16456 -> [])))))
                 in
              FStar_List.append order1 uu____16403  in
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
                   let uu____16486 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16488 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16488
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16486
                   then
                     let uu____16493 =
                       let uu____16498 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16498)
                        in
                     let uu____16499 = get_range env  in
                     FStar_Errors.raise_error uu____16493 uu____16499
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16576 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16576
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16625 =
                                              let uu____16634 =
                                                find_edge order2 (i, k)  in
                                              let uu____16637 =
                                                find_edge order2 (j, k)  in
                                              (uu____16634, uu____16637)  in
                                            match uu____16625 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16679,uu____16680)
                                                     ->
                                                     let uu____16687 =
                                                       let uu____16692 =
                                                         let uu____16693 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16693
                                                          in
                                                       let uu____16696 =
                                                         let uu____16697 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16697
                                                          in
                                                       (uu____16692,
                                                         uu____16696)
                                                        in
                                                     (match uu____16687 with
                                                      | (true ,true ) ->
                                                          let uu____16708 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16708
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
                                            | uu____16733 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___123_16806 = env.effects  in
              { decls = (uu___123_16806.decls); order = order2; joins }  in
            let uu___124_16807 = env  in
            {
              solver = (uu___124_16807.solver);
              range = (uu___124_16807.range);
              curmodule = (uu___124_16807.curmodule);
              gamma = (uu___124_16807.gamma);
              gamma_sig = (uu___124_16807.gamma_sig);
              gamma_cache = (uu___124_16807.gamma_cache);
              modules = (uu___124_16807.modules);
              expected_typ = (uu___124_16807.expected_typ);
              sigtab = (uu___124_16807.sigtab);
              is_pattern = (uu___124_16807.is_pattern);
              instantiate_imp = (uu___124_16807.instantiate_imp);
              effects;
              generalize = (uu___124_16807.generalize);
              letrecs = (uu___124_16807.letrecs);
              top_level = (uu___124_16807.top_level);
              check_uvars = (uu___124_16807.check_uvars);
              use_eq = (uu___124_16807.use_eq);
              is_iface = (uu___124_16807.is_iface);
              admit = (uu___124_16807.admit);
              lax = (uu___124_16807.lax);
              lax_universes = (uu___124_16807.lax_universes);
              failhard = (uu___124_16807.failhard);
              nosynth = (uu___124_16807.nosynth);
              uvar_subtyping = (uu___124_16807.uvar_subtyping);
              tc_term = (uu___124_16807.tc_term);
              type_of = (uu___124_16807.type_of);
              universe_of = (uu___124_16807.universe_of);
              check_type_of = (uu___124_16807.check_type_of);
              use_bv_sorts = (uu___124_16807.use_bv_sorts);
              qtbl_name_and_index = (uu___124_16807.qtbl_name_and_index);
              normalized_eff_names = (uu___124_16807.normalized_eff_names);
              proof_ns = (uu___124_16807.proof_ns);
              synth_hook = (uu___124_16807.synth_hook);
              splice = (uu___124_16807.splice);
              is_native_tactic = (uu___124_16807.is_native_tactic);
              identifier_info = (uu___124_16807.identifier_info);
              tc_hooks = (uu___124_16807.tc_hooks);
              dsenv = (uu___124_16807.dsenv);
              dep_graph = (uu___124_16807.dep_graph)
            }))
      | uu____16808 -> env
  
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
        | uu____16836 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16848 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16848 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16865 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16865 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16884 =
                     let uu____16889 =
                       let uu____16890 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16895 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16902 =
                         let uu____16903 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16903  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16890 uu____16895 uu____16902
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16889)
                      in
                   FStar_Errors.raise_error uu____16884
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16908 =
                     let uu____16917 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16917 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16946  ->
                        fun uu____16947  ->
                          match (uu____16946, uu____16947) with
                          | ((x,uu____16969),(t,uu____16971)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16908
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____16990 =
                     let uu___125_16991 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_16991.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_16991.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_16991.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_16991.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____16990
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
          let uu____17021 = effect_decl_opt env effect_name  in
          match uu____17021 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____17054 =
                only_reifiable &&
                  (let uu____17056 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____17056)
                 in
              if uu____17054
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____17072 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____17091 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____17120 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____17120
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____17121 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____17121
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____17133 =
                       let uu____17136 = get_range env  in
                       let uu____17137 =
                         let uu____17144 =
                           let uu____17145 =
                             let uu____17160 =
                               let uu____17169 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____17169; wp]  in
                             (repr, uu____17160)  in
                           FStar_Syntax_Syntax.Tm_app uu____17145  in
                         FStar_Syntax_Syntax.mk uu____17144  in
                       uu____17137 FStar_Pervasives_Native.None uu____17136
                        in
                     FStar_Pervasives_Native.Some uu____17133)
  
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
          let uu____17249 =
            let uu____17254 =
              let uu____17255 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____17255
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____17254)  in
          let uu____17256 = get_range env  in
          FStar_Errors.raise_error uu____17249 uu____17256  in
        let uu____17257 = effect_repr_aux true env c u_c  in
        match uu____17257 with
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
      | uu____17303 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____17314 =
        let uu____17315 = FStar_Syntax_Subst.compress t  in
        uu____17315.FStar_Syntax_Syntax.n  in
      match uu____17314 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____17318,c) ->
          is_reifiable_comp env c
      | uu____17336 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___126_17357 = env  in
        {
          solver = (uu___126_17357.solver);
          range = (uu___126_17357.range);
          curmodule = (uu___126_17357.curmodule);
          gamma = (uu___126_17357.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___126_17357.gamma_cache);
          modules = (uu___126_17357.modules);
          expected_typ = (uu___126_17357.expected_typ);
          sigtab = (uu___126_17357.sigtab);
          is_pattern = (uu___126_17357.is_pattern);
          instantiate_imp = (uu___126_17357.instantiate_imp);
          effects = (uu___126_17357.effects);
          generalize = (uu___126_17357.generalize);
          letrecs = (uu___126_17357.letrecs);
          top_level = (uu___126_17357.top_level);
          check_uvars = (uu___126_17357.check_uvars);
          use_eq = (uu___126_17357.use_eq);
          is_iface = (uu___126_17357.is_iface);
          admit = (uu___126_17357.admit);
          lax = (uu___126_17357.lax);
          lax_universes = (uu___126_17357.lax_universes);
          failhard = (uu___126_17357.failhard);
          nosynth = (uu___126_17357.nosynth);
          uvar_subtyping = (uu___126_17357.uvar_subtyping);
          tc_term = (uu___126_17357.tc_term);
          type_of = (uu___126_17357.type_of);
          universe_of = (uu___126_17357.universe_of);
          check_type_of = (uu___126_17357.check_type_of);
          use_bv_sorts = (uu___126_17357.use_bv_sorts);
          qtbl_name_and_index = (uu___126_17357.qtbl_name_and_index);
          normalized_eff_names = (uu___126_17357.normalized_eff_names);
          proof_ns = (uu___126_17357.proof_ns);
          synth_hook = (uu___126_17357.synth_hook);
          splice = (uu___126_17357.splice);
          is_native_tactic = (uu___126_17357.is_native_tactic);
          identifier_info = (uu___126_17357.identifier_info);
          tc_hooks = (uu___126_17357.tc_hooks);
          dsenv = (uu___126_17357.dsenv);
          dep_graph = (uu___126_17357.dep_graph)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___127_17369 = env  in
      {
        solver = (uu___127_17369.solver);
        range = (uu___127_17369.range);
        curmodule = (uu___127_17369.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___127_17369.gamma_sig);
        gamma_cache = (uu___127_17369.gamma_cache);
        modules = (uu___127_17369.modules);
        expected_typ = (uu___127_17369.expected_typ);
        sigtab = (uu___127_17369.sigtab);
        is_pattern = (uu___127_17369.is_pattern);
        instantiate_imp = (uu___127_17369.instantiate_imp);
        effects = (uu___127_17369.effects);
        generalize = (uu___127_17369.generalize);
        letrecs = (uu___127_17369.letrecs);
        top_level = (uu___127_17369.top_level);
        check_uvars = (uu___127_17369.check_uvars);
        use_eq = (uu___127_17369.use_eq);
        is_iface = (uu___127_17369.is_iface);
        admit = (uu___127_17369.admit);
        lax = (uu___127_17369.lax);
        lax_universes = (uu___127_17369.lax_universes);
        failhard = (uu___127_17369.failhard);
        nosynth = (uu___127_17369.nosynth);
        uvar_subtyping = (uu___127_17369.uvar_subtyping);
        tc_term = (uu___127_17369.tc_term);
        type_of = (uu___127_17369.type_of);
        universe_of = (uu___127_17369.universe_of);
        check_type_of = (uu___127_17369.check_type_of);
        use_bv_sorts = (uu___127_17369.use_bv_sorts);
        qtbl_name_and_index = (uu___127_17369.qtbl_name_and_index);
        normalized_eff_names = (uu___127_17369.normalized_eff_names);
        proof_ns = (uu___127_17369.proof_ns);
        synth_hook = (uu___127_17369.synth_hook);
        splice = (uu___127_17369.splice);
        is_native_tactic = (uu___127_17369.is_native_tactic);
        identifier_info = (uu___127_17369.identifier_info);
        tc_hooks = (uu___127_17369.tc_hooks);
        dsenv = (uu___127_17369.dsenv);
        dep_graph = (uu___127_17369.dep_graph)
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
            (let uu___128_17424 = env  in
             {
               solver = (uu___128_17424.solver);
               range = (uu___128_17424.range);
               curmodule = (uu___128_17424.curmodule);
               gamma = rest;
               gamma_sig = (uu___128_17424.gamma_sig);
               gamma_cache = (uu___128_17424.gamma_cache);
               modules = (uu___128_17424.modules);
               expected_typ = (uu___128_17424.expected_typ);
               sigtab = (uu___128_17424.sigtab);
               is_pattern = (uu___128_17424.is_pattern);
               instantiate_imp = (uu___128_17424.instantiate_imp);
               effects = (uu___128_17424.effects);
               generalize = (uu___128_17424.generalize);
               letrecs = (uu___128_17424.letrecs);
               top_level = (uu___128_17424.top_level);
               check_uvars = (uu___128_17424.check_uvars);
               use_eq = (uu___128_17424.use_eq);
               is_iface = (uu___128_17424.is_iface);
               admit = (uu___128_17424.admit);
               lax = (uu___128_17424.lax);
               lax_universes = (uu___128_17424.lax_universes);
               failhard = (uu___128_17424.failhard);
               nosynth = (uu___128_17424.nosynth);
               uvar_subtyping = (uu___128_17424.uvar_subtyping);
               tc_term = (uu___128_17424.tc_term);
               type_of = (uu___128_17424.type_of);
               universe_of = (uu___128_17424.universe_of);
               check_type_of = (uu___128_17424.check_type_of);
               use_bv_sorts = (uu___128_17424.use_bv_sorts);
               qtbl_name_and_index = (uu___128_17424.qtbl_name_and_index);
               normalized_eff_names = (uu___128_17424.normalized_eff_names);
               proof_ns = (uu___128_17424.proof_ns);
               synth_hook = (uu___128_17424.synth_hook);
               splice = (uu___128_17424.splice);
               is_native_tactic = (uu___128_17424.is_native_tactic);
               identifier_info = (uu___128_17424.identifier_info);
               tc_hooks = (uu___128_17424.tc_hooks);
               dsenv = (uu___128_17424.dsenv);
               dep_graph = (uu___128_17424.dep_graph)
             }))
    | uu____17425 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17451  ->
             match uu____17451 with | (x,uu____17457) -> push_bv env1 x) env
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
            let uu___129_17487 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_17487.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_17487.FStar_Syntax_Syntax.index);
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
      (let uu___130_17527 = env  in
       {
         solver = (uu___130_17527.solver);
         range = (uu___130_17527.range);
         curmodule = (uu___130_17527.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___130_17527.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_17527.sigtab);
         is_pattern = (uu___130_17527.is_pattern);
         instantiate_imp = (uu___130_17527.instantiate_imp);
         effects = (uu___130_17527.effects);
         generalize = (uu___130_17527.generalize);
         letrecs = (uu___130_17527.letrecs);
         top_level = (uu___130_17527.top_level);
         check_uvars = (uu___130_17527.check_uvars);
         use_eq = (uu___130_17527.use_eq);
         is_iface = (uu___130_17527.is_iface);
         admit = (uu___130_17527.admit);
         lax = (uu___130_17527.lax);
         lax_universes = (uu___130_17527.lax_universes);
         failhard = (uu___130_17527.failhard);
         nosynth = (uu___130_17527.nosynth);
         uvar_subtyping = (uu___130_17527.uvar_subtyping);
         tc_term = (uu___130_17527.tc_term);
         type_of = (uu___130_17527.type_of);
         universe_of = (uu___130_17527.universe_of);
         check_type_of = (uu___130_17527.check_type_of);
         use_bv_sorts = (uu___130_17527.use_bv_sorts);
         qtbl_name_and_index = (uu___130_17527.qtbl_name_and_index);
         normalized_eff_names = (uu___130_17527.normalized_eff_names);
         proof_ns = (uu___130_17527.proof_ns);
         synth_hook = (uu___130_17527.synth_hook);
         splice = (uu___130_17527.splice);
         is_native_tactic = (uu___130_17527.is_native_tactic);
         identifier_info = (uu___130_17527.identifier_info);
         tc_hooks = (uu___130_17527.tc_hooks);
         dsenv = (uu___130_17527.dsenv);
         dep_graph = (uu___130_17527.dep_graph)
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
        let uu____17569 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17569 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17597 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17597)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___131_17612 = env  in
      {
        solver = (uu___131_17612.solver);
        range = (uu___131_17612.range);
        curmodule = (uu___131_17612.curmodule);
        gamma = (uu___131_17612.gamma);
        gamma_sig = (uu___131_17612.gamma_sig);
        gamma_cache = (uu___131_17612.gamma_cache);
        modules = (uu___131_17612.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_17612.sigtab);
        is_pattern = (uu___131_17612.is_pattern);
        instantiate_imp = (uu___131_17612.instantiate_imp);
        effects = (uu___131_17612.effects);
        generalize = (uu___131_17612.generalize);
        letrecs = (uu___131_17612.letrecs);
        top_level = (uu___131_17612.top_level);
        check_uvars = (uu___131_17612.check_uvars);
        use_eq = false;
        is_iface = (uu___131_17612.is_iface);
        admit = (uu___131_17612.admit);
        lax = (uu___131_17612.lax);
        lax_universes = (uu___131_17612.lax_universes);
        failhard = (uu___131_17612.failhard);
        nosynth = (uu___131_17612.nosynth);
        uvar_subtyping = (uu___131_17612.uvar_subtyping);
        tc_term = (uu___131_17612.tc_term);
        type_of = (uu___131_17612.type_of);
        universe_of = (uu___131_17612.universe_of);
        check_type_of = (uu___131_17612.check_type_of);
        use_bv_sorts = (uu___131_17612.use_bv_sorts);
        qtbl_name_and_index = (uu___131_17612.qtbl_name_and_index);
        normalized_eff_names = (uu___131_17612.normalized_eff_names);
        proof_ns = (uu___131_17612.proof_ns);
        synth_hook = (uu___131_17612.synth_hook);
        splice = (uu___131_17612.splice);
        is_native_tactic = (uu___131_17612.is_native_tactic);
        identifier_info = (uu___131_17612.identifier_info);
        tc_hooks = (uu___131_17612.tc_hooks);
        dsenv = (uu___131_17612.dsenv);
        dep_graph = (uu___131_17612.dep_graph)
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
    let uu____17640 = expected_typ env_  in
    ((let uu___132_17646 = env_  in
      {
        solver = (uu___132_17646.solver);
        range = (uu___132_17646.range);
        curmodule = (uu___132_17646.curmodule);
        gamma = (uu___132_17646.gamma);
        gamma_sig = (uu___132_17646.gamma_sig);
        gamma_cache = (uu___132_17646.gamma_cache);
        modules = (uu___132_17646.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_17646.sigtab);
        is_pattern = (uu___132_17646.is_pattern);
        instantiate_imp = (uu___132_17646.instantiate_imp);
        effects = (uu___132_17646.effects);
        generalize = (uu___132_17646.generalize);
        letrecs = (uu___132_17646.letrecs);
        top_level = (uu___132_17646.top_level);
        check_uvars = (uu___132_17646.check_uvars);
        use_eq = false;
        is_iface = (uu___132_17646.is_iface);
        admit = (uu___132_17646.admit);
        lax = (uu___132_17646.lax);
        lax_universes = (uu___132_17646.lax_universes);
        failhard = (uu___132_17646.failhard);
        nosynth = (uu___132_17646.nosynth);
        uvar_subtyping = (uu___132_17646.uvar_subtyping);
        tc_term = (uu___132_17646.tc_term);
        type_of = (uu___132_17646.type_of);
        universe_of = (uu___132_17646.universe_of);
        check_type_of = (uu___132_17646.check_type_of);
        use_bv_sorts = (uu___132_17646.use_bv_sorts);
        qtbl_name_and_index = (uu___132_17646.qtbl_name_and_index);
        normalized_eff_names = (uu___132_17646.normalized_eff_names);
        proof_ns = (uu___132_17646.proof_ns);
        synth_hook = (uu___132_17646.synth_hook);
        splice = (uu___132_17646.splice);
        is_native_tactic = (uu___132_17646.is_native_tactic);
        identifier_info = (uu___132_17646.identifier_info);
        tc_hooks = (uu___132_17646.tc_hooks);
        dsenv = (uu___132_17646.dsenv);
        dep_graph = (uu___132_17646.dep_graph)
      }), uu____17640)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17656 =
      let uu____17659 = FStar_Ident.id_of_text ""  in [uu____17659]  in
    FStar_Ident.lid_of_ids uu____17656  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17665 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17665
        then
          let uu____17668 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____17668 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___133_17695 = env  in
       {
         solver = (uu___133_17695.solver);
         range = (uu___133_17695.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___133_17695.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_17695.expected_typ);
         sigtab = (uu___133_17695.sigtab);
         is_pattern = (uu___133_17695.is_pattern);
         instantiate_imp = (uu___133_17695.instantiate_imp);
         effects = (uu___133_17695.effects);
         generalize = (uu___133_17695.generalize);
         letrecs = (uu___133_17695.letrecs);
         top_level = (uu___133_17695.top_level);
         check_uvars = (uu___133_17695.check_uvars);
         use_eq = (uu___133_17695.use_eq);
         is_iface = (uu___133_17695.is_iface);
         admit = (uu___133_17695.admit);
         lax = (uu___133_17695.lax);
         lax_universes = (uu___133_17695.lax_universes);
         failhard = (uu___133_17695.failhard);
         nosynth = (uu___133_17695.nosynth);
         uvar_subtyping = (uu___133_17695.uvar_subtyping);
         tc_term = (uu___133_17695.tc_term);
         type_of = (uu___133_17695.type_of);
         universe_of = (uu___133_17695.universe_of);
         check_type_of = (uu___133_17695.check_type_of);
         use_bv_sorts = (uu___133_17695.use_bv_sorts);
         qtbl_name_and_index = (uu___133_17695.qtbl_name_and_index);
         normalized_eff_names = (uu___133_17695.normalized_eff_names);
         proof_ns = (uu___133_17695.proof_ns);
         synth_hook = (uu___133_17695.synth_hook);
         splice = (uu___133_17695.splice);
         is_native_tactic = (uu___133_17695.is_native_tactic);
         identifier_info = (uu___133_17695.identifier_info);
         tc_hooks = (uu___133_17695.tc_hooks);
         dsenv = (uu___133_17695.dsenv);
         dep_graph = (uu___133_17695.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17746)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17750,(uu____17751,t)))::tl1
          ->
          let uu____17772 =
            let uu____17775 = FStar_Syntax_Free.uvars t  in
            ext out uu____17775  in
          aux uu____17772 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17778;
            FStar_Syntax_Syntax.index = uu____17779;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17786 =
            let uu____17789 = FStar_Syntax_Free.uvars t  in
            ext out uu____17789  in
          aux uu____17786 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____17846)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17850,(uu____17851,t)))::tl1
          ->
          let uu____17872 =
            let uu____17875 = FStar_Syntax_Free.univs t  in
            ext out uu____17875  in
          aux uu____17872 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17878;
            FStar_Syntax_Syntax.index = uu____17879;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17886 =
            let uu____17889 = FStar_Syntax_Free.univs t  in
            ext out uu____17889  in
          aux uu____17886 tl1
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
          let uu____17950 = FStar_Util.set_add uname out  in
          aux uu____17950 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____17953,(uu____17954,t)))::tl1
          ->
          let uu____17975 =
            let uu____17978 = FStar_Syntax_Free.univnames t  in
            ext out uu____17978  in
          aux uu____17975 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17981;
            FStar_Syntax_Syntax.index = uu____17982;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17989 =
            let uu____17992 = FStar_Syntax_Free.univnames t  in
            ext out uu____17992  in
          aux uu____17989 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___107_18012  ->
            match uu___107_18012 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18016 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____18029 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____18039 =
      let uu____18046 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____18046
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____18039 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____18084 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___108_18094  ->
              match uu___108_18094 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____18096 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____18096
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____18099) ->
                  let uu____18116 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____18116))
       in
    FStar_All.pipe_right uu____18084 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___109_18123  ->
    match uu___109_18123 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____18124 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18144  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18186) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18205,uu____18206) -> false  in
      let uu____18215 =
        FStar_List.tryFind
          (fun uu____18233  ->
             match uu____18233 with | (p,uu____18241) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18215 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18252,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18274 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18274
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___134_18292 = e  in
        {
          solver = (uu___134_18292.solver);
          range = (uu___134_18292.range);
          curmodule = (uu___134_18292.curmodule);
          gamma = (uu___134_18292.gamma);
          gamma_sig = (uu___134_18292.gamma_sig);
          gamma_cache = (uu___134_18292.gamma_cache);
          modules = (uu___134_18292.modules);
          expected_typ = (uu___134_18292.expected_typ);
          sigtab = (uu___134_18292.sigtab);
          is_pattern = (uu___134_18292.is_pattern);
          instantiate_imp = (uu___134_18292.instantiate_imp);
          effects = (uu___134_18292.effects);
          generalize = (uu___134_18292.generalize);
          letrecs = (uu___134_18292.letrecs);
          top_level = (uu___134_18292.top_level);
          check_uvars = (uu___134_18292.check_uvars);
          use_eq = (uu___134_18292.use_eq);
          is_iface = (uu___134_18292.is_iface);
          admit = (uu___134_18292.admit);
          lax = (uu___134_18292.lax);
          lax_universes = (uu___134_18292.lax_universes);
          failhard = (uu___134_18292.failhard);
          nosynth = (uu___134_18292.nosynth);
          uvar_subtyping = (uu___134_18292.uvar_subtyping);
          tc_term = (uu___134_18292.tc_term);
          type_of = (uu___134_18292.type_of);
          universe_of = (uu___134_18292.universe_of);
          check_type_of = (uu___134_18292.check_type_of);
          use_bv_sorts = (uu___134_18292.use_bv_sorts);
          qtbl_name_and_index = (uu___134_18292.qtbl_name_and_index);
          normalized_eff_names = (uu___134_18292.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___134_18292.synth_hook);
          splice = (uu___134_18292.splice);
          is_native_tactic = (uu___134_18292.is_native_tactic);
          identifier_info = (uu___134_18292.identifier_info);
          tc_hooks = (uu___134_18292.tc_hooks);
          dsenv = (uu___134_18292.dsenv);
          dep_graph = (uu___134_18292.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___135_18332 = e  in
      {
        solver = (uu___135_18332.solver);
        range = (uu___135_18332.range);
        curmodule = (uu___135_18332.curmodule);
        gamma = (uu___135_18332.gamma);
        gamma_sig = (uu___135_18332.gamma_sig);
        gamma_cache = (uu___135_18332.gamma_cache);
        modules = (uu___135_18332.modules);
        expected_typ = (uu___135_18332.expected_typ);
        sigtab = (uu___135_18332.sigtab);
        is_pattern = (uu___135_18332.is_pattern);
        instantiate_imp = (uu___135_18332.instantiate_imp);
        effects = (uu___135_18332.effects);
        generalize = (uu___135_18332.generalize);
        letrecs = (uu___135_18332.letrecs);
        top_level = (uu___135_18332.top_level);
        check_uvars = (uu___135_18332.check_uvars);
        use_eq = (uu___135_18332.use_eq);
        is_iface = (uu___135_18332.is_iface);
        admit = (uu___135_18332.admit);
        lax = (uu___135_18332.lax);
        lax_universes = (uu___135_18332.lax_universes);
        failhard = (uu___135_18332.failhard);
        nosynth = (uu___135_18332.nosynth);
        uvar_subtyping = (uu___135_18332.uvar_subtyping);
        tc_term = (uu___135_18332.tc_term);
        type_of = (uu___135_18332.type_of);
        universe_of = (uu___135_18332.universe_of);
        check_type_of = (uu___135_18332.check_type_of);
        use_bv_sorts = (uu___135_18332.use_bv_sorts);
        qtbl_name_and_index = (uu___135_18332.qtbl_name_and_index);
        normalized_eff_names = (uu___135_18332.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___135_18332.synth_hook);
        splice = (uu___135_18332.splice);
        is_native_tactic = (uu___135_18332.is_native_tactic);
        identifier_info = (uu___135_18332.identifier_info);
        tc_hooks = (uu___135_18332.tc_hooks);
        dsenv = (uu___135_18332.dsenv);
        dep_graph = (uu___135_18332.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18347 = FStar_Syntax_Free.names t  in
      let uu____18350 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18347 uu____18350
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18371 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18371
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18379 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18379
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18398 =
      match uu____18398 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18414 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18414)
       in
    let uu____18416 =
      let uu____18419 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18419 FStar_List.rev  in
    FStar_All.pipe_right uu____18416 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18434  -> ());
    push = (fun uu____18436  -> ());
    pop = (fun uu____18438  -> ());
    snapshot =
      (fun uu____18440  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18449  -> fun uu____18450  -> ());
    encode_modul = (fun uu____18461  -> fun uu____18462  -> ());
    encode_sig = (fun uu____18465  -> fun uu____18466  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18472 =
             let uu____18479 = FStar_Options.peek ()  in (e, g, uu____18479)
              in
           [uu____18472]);
    solve = (fun uu____18495  -> fun uu____18496  -> fun uu____18497  -> ());
    finish = (fun uu____18503  -> ());
    refresh = (fun uu____18505  -> ())
  } 