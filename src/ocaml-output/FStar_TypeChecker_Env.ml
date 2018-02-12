open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv 
  | Binding_lid of (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2 
  | Binding_sig of (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
  FStar_Pervasives_Native.tuple2 
  | Binding_univ of FStar_Syntax_Syntax.univ_name 
  | Binding_sig_inst of
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____43 -> false
  
let (__proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____59 -> false
  
let (__proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_sig : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____89 -> false
  
let (__proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____119 -> false
  
let (__proj__Binding_univ__item___0 :
  binding -> FStar_Syntax_Syntax.univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Binding_sig_inst : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____139 -> false
  
let (__proj__Binding_sig_inst__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0 
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac [@@deriving show]
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____178 -> false
  
let (uu___is_Inlining : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____182 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____186 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____191 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
let (uu___is_UnfoldTac : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____202 -> false
  
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
  gamma: binding Prims.list ;
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
  qname_and_index:
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
    ;
  proof_ns: proof_namespace ;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_ToSyntax_Env.env ;
  dep_graph: FStar_Parser_Dep.deps }[@@deriving show]
and solver_t =
  {
  init: env -> Prims.unit ;
  push: Prims.string -> Prims.unit ;
  pop: Prims.string -> Prims.unit ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit ;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
    ;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
    ;
  finish: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit }[@@deriving show]
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
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
    }[@@deriving show]
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> Prims.unit }[@@deriving show]
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
  
let (__proj__Mkenv__item__gamma : env -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__sigtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__admit
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax_universes
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_bv_sorts
  
let (__proj__Mkenv__item__qname_and_index :
  env ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qname_and_index
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__proof_ns
  
let (__proj__Mkenv__item__synth :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_ToSyntax_Env.env) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dsenv
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
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
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
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
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> Prims.unit -> Prims.unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh :
  solver_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
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
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks -> env -> binding -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
let (rename_gamma :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___70_5655  ->
              match uu___70_5655 with
              | Binding_var x ->
                  let y =
                    let uu____5658 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____5658  in
                  let uu____5659 =
                    let uu____5660 = FStar_Syntax_Subst.compress y  in
                    uu____5660.FStar_Syntax_Syntax.n  in
                  (match uu____5659 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5664 =
                         let uu___85_5665 = y1  in
                         let uu____5666 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___85_5665.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___85_5665.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5666
                         }  in
                       Binding_var uu____5664
                   | uu____5669 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___86_5677 = env  in
      let uu____5678 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___86_5677.solver);
        range = (uu___86_5677.range);
        curmodule = (uu___86_5677.curmodule);
        gamma = uu____5678;
        gamma_cache = (uu___86_5677.gamma_cache);
        modules = (uu___86_5677.modules);
        expected_typ = (uu___86_5677.expected_typ);
        sigtab = (uu___86_5677.sigtab);
        is_pattern = (uu___86_5677.is_pattern);
        instantiate_imp = (uu___86_5677.instantiate_imp);
        effects = (uu___86_5677.effects);
        generalize = (uu___86_5677.generalize);
        letrecs = (uu___86_5677.letrecs);
        top_level = (uu___86_5677.top_level);
        check_uvars = (uu___86_5677.check_uvars);
        use_eq = (uu___86_5677.use_eq);
        is_iface = (uu___86_5677.is_iface);
        admit = (uu___86_5677.admit);
        lax = (uu___86_5677.lax);
        lax_universes = (uu___86_5677.lax_universes);
        failhard = (uu___86_5677.failhard);
        nosynth = (uu___86_5677.nosynth);
        tc_term = (uu___86_5677.tc_term);
        type_of = (uu___86_5677.type_of);
        universe_of = (uu___86_5677.universe_of);
        check_type_of = (uu___86_5677.check_type_of);
        use_bv_sorts = (uu___86_5677.use_bv_sorts);
        qname_and_index = (uu___86_5677.qname_and_index);
        proof_ns = (uu___86_5677.proof_ns);
        synth = (uu___86_5677.synth);
        is_native_tactic = (uu___86_5677.is_native_tactic);
        identifier_info = (uu___86_5677.identifier_info);
        tc_hooks = (uu___86_5677.tc_hooks);
        dsenv = (uu___86_5677.dsenv);
        dep_graph = (uu___86_5677.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____5685  -> fun uu____5686  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___87_5696 = env  in
      {
        solver = (uu___87_5696.solver);
        range = (uu___87_5696.range);
        curmodule = (uu___87_5696.curmodule);
        gamma = (uu___87_5696.gamma);
        gamma_cache = (uu___87_5696.gamma_cache);
        modules = (uu___87_5696.modules);
        expected_typ = (uu___87_5696.expected_typ);
        sigtab = (uu___87_5696.sigtab);
        is_pattern = (uu___87_5696.is_pattern);
        instantiate_imp = (uu___87_5696.instantiate_imp);
        effects = (uu___87_5696.effects);
        generalize = (uu___87_5696.generalize);
        letrecs = (uu___87_5696.letrecs);
        top_level = (uu___87_5696.top_level);
        check_uvars = (uu___87_5696.check_uvars);
        use_eq = (uu___87_5696.use_eq);
        is_iface = (uu___87_5696.is_iface);
        admit = (uu___87_5696.admit);
        lax = (uu___87_5696.lax);
        lax_universes = (uu___87_5696.lax_universes);
        failhard = (uu___87_5696.failhard);
        nosynth = (uu___87_5696.nosynth);
        tc_term = (uu___87_5696.tc_term);
        type_of = (uu___87_5696.type_of);
        universe_of = (uu___87_5696.universe_of);
        check_type_of = (uu___87_5696.check_type_of);
        use_bv_sorts = (uu___87_5696.use_bv_sorts);
        qname_and_index = (uu___87_5696.qname_and_index);
        proof_ns = (uu___87_5696.proof_ns);
        synth = (uu___87_5696.synth);
        is_native_tactic = (uu___87_5696.is_native_tactic);
        identifier_info = (uu___87_5696.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___87_5696.dsenv);
        dep_graph = (uu___87_5696.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___88_5703 = e  in
      {
        solver = (uu___88_5703.solver);
        range = (uu___88_5703.range);
        curmodule = (uu___88_5703.curmodule);
        gamma = (uu___88_5703.gamma);
        gamma_cache = (uu___88_5703.gamma_cache);
        modules = (uu___88_5703.modules);
        expected_typ = (uu___88_5703.expected_typ);
        sigtab = (uu___88_5703.sigtab);
        is_pattern = (uu___88_5703.is_pattern);
        instantiate_imp = (uu___88_5703.instantiate_imp);
        effects = (uu___88_5703.effects);
        generalize = (uu___88_5703.generalize);
        letrecs = (uu___88_5703.letrecs);
        top_level = (uu___88_5703.top_level);
        check_uvars = (uu___88_5703.check_uvars);
        use_eq = (uu___88_5703.use_eq);
        is_iface = (uu___88_5703.is_iface);
        admit = (uu___88_5703.admit);
        lax = (uu___88_5703.lax);
        lax_universes = (uu___88_5703.lax_universes);
        failhard = (uu___88_5703.failhard);
        nosynth = (uu___88_5703.nosynth);
        tc_term = (uu___88_5703.tc_term);
        type_of = (uu___88_5703.type_of);
        universe_of = (uu___88_5703.universe_of);
        check_type_of = (uu___88_5703.check_type_of);
        use_bv_sorts = (uu___88_5703.use_bv_sorts);
        qname_and_index = (uu___88_5703.qname_and_index);
        proof_ns = (uu___88_5703.proof_ns);
        synth = (uu___88_5703.synth);
        is_native_tactic = (uu___88_5703.is_native_tactic);
        identifier_info = (uu___88_5703.identifier_info);
        tc_hooks = (uu___88_5703.tc_hooks);
        dsenv = (uu___88_5703.dsenv);
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
      | (NoDelta ,uu____5718) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5719,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5720,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5721 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____5728 . Prims.unit -> 'Auu____5728 FStar_Util.smap =
  fun uu____5734  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____5737 . Prims.unit -> 'Auu____5737 FStar_Util.smap =
  fun uu____5743  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____5839 = new_gamma_cache ()  in
                let uu____5842 = new_sigtab ()  in
                let uu____5845 = FStar_Options.using_facts_from ()  in
                let uu____5846 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____5849 = FStar_ToSyntax_Env.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____5839;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____5842;
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
                  qname_and_index = FStar_Pervasives_Native.None;
                  proof_ns = uu____5845;
                  synth =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  is_native_tactic = (fun uu____5883  -> false);
                  identifier_info = uu____5846;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____5849;
                  dep_graph = deps
                }
  
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6041  ->
    let uu____6042 = FStar_ST.op_Bang query_indices  in
    match uu____6042 with
    | [] -> failwith "Empty query indices!"
    | uu____6092 ->
        let uu____6101 =
          let uu____6110 =
            let uu____6117 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____6117  in
          let uu____6167 = FStar_ST.op_Bang query_indices  in uu____6110 ::
            uu____6167
           in
        FStar_ST.op_Colon_Equals query_indices uu____6101
  
let (pop_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6254  ->
    let uu____6255 = FStar_ST.op_Bang query_indices  in
    match uu____6255 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____6368  ->
    match uu____6368 with
    | (l,n1) ->
        let uu____6375 = FStar_ST.op_Bang query_indices  in
        (match uu____6375 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6486 -> failwith "Empty query indices")
  
let (peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6503  ->
    let uu____6504 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6504
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____6601 =
       let uu____6604 = FStar_ST.op_Bang stack  in env :: uu____6604  in
     FStar_ST.op_Colon_Equals stack uu____6601);
    (let uu___89_6653 = env  in
     let uu____6654 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6657 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6660 =
       let uu____6663 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6663  in
     {
       solver = (uu___89_6653.solver);
       range = (uu___89_6653.range);
       curmodule = (uu___89_6653.curmodule);
       gamma = (uu___89_6653.gamma);
       gamma_cache = uu____6654;
       modules = (uu___89_6653.modules);
       expected_typ = (uu___89_6653.expected_typ);
       sigtab = uu____6657;
       is_pattern = (uu___89_6653.is_pattern);
       instantiate_imp = (uu___89_6653.instantiate_imp);
       effects = (uu___89_6653.effects);
       generalize = (uu___89_6653.generalize);
       letrecs = (uu___89_6653.letrecs);
       top_level = (uu___89_6653.top_level);
       check_uvars = (uu___89_6653.check_uvars);
       use_eq = (uu___89_6653.use_eq);
       is_iface = (uu___89_6653.is_iface);
       admit = (uu___89_6653.admit);
       lax = (uu___89_6653.lax);
       lax_universes = (uu___89_6653.lax_universes);
       failhard = (uu___89_6653.failhard);
       nosynth = (uu___89_6653.nosynth);
       tc_term = (uu___89_6653.tc_term);
       type_of = (uu___89_6653.type_of);
       universe_of = (uu___89_6653.universe_of);
       check_type_of = (uu___89_6653.check_type_of);
       use_bv_sorts = (uu___89_6653.use_bv_sorts);
       qname_and_index = (uu___89_6653.qname_and_index);
       proof_ns = (uu___89_6653.proof_ns);
       synth = (uu___89_6653.synth);
       is_native_tactic = (uu___89_6653.is_native_tactic);
       identifier_info = uu____6660;
       tc_hooks = (uu___89_6653.tc_hooks);
       dsenv = (uu___89_6653.dsenv);
       dep_graph = (uu___89_6653.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____6759  ->
    let uu____6760 = FStar_ST.op_Bang stack  in
    match uu____6760 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6814 -> failwith "Impossible: Too many pops"
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____6853 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6879  ->
                  match uu____6879 with
                  | (m,uu____6885) -> FStar_Ident.lid_equals l m))
           in
        (match uu____6853 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___90_6892 = env  in
               {
                 solver = (uu___90_6892.solver);
                 range = (uu___90_6892.range);
                 curmodule = (uu___90_6892.curmodule);
                 gamma = (uu___90_6892.gamma);
                 gamma_cache = (uu___90_6892.gamma_cache);
                 modules = (uu___90_6892.modules);
                 expected_typ = (uu___90_6892.expected_typ);
                 sigtab = (uu___90_6892.sigtab);
                 is_pattern = (uu___90_6892.is_pattern);
                 instantiate_imp = (uu___90_6892.instantiate_imp);
                 effects = (uu___90_6892.effects);
                 generalize = (uu___90_6892.generalize);
                 letrecs = (uu___90_6892.letrecs);
                 top_level = (uu___90_6892.top_level);
                 check_uvars = (uu___90_6892.check_uvars);
                 use_eq = (uu___90_6892.use_eq);
                 is_iface = (uu___90_6892.is_iface);
                 admit = (uu___90_6892.admit);
                 lax = (uu___90_6892.lax);
                 lax_universes = (uu___90_6892.lax_universes);
                 failhard = (uu___90_6892.failhard);
                 nosynth = (uu___90_6892.nosynth);
                 tc_term = (uu___90_6892.tc_term);
                 type_of = (uu___90_6892.type_of);
                 universe_of = (uu___90_6892.universe_of);
                 check_type_of = (uu___90_6892.check_type_of);
                 use_bv_sorts = (uu___90_6892.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___90_6892.proof_ns);
                 synth = (uu___90_6892.synth);
                 is_native_tactic = (uu___90_6892.is_native_tactic);
                 identifier_info = (uu___90_6892.identifier_info);
                 tc_hooks = (uu___90_6892.tc_hooks);
                 dsenv = (uu___90_6892.dsenv);
                 dep_graph = (uu___90_6892.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6897,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___91_6905 = env  in
               {
                 solver = (uu___91_6905.solver);
                 range = (uu___91_6905.range);
                 curmodule = (uu___91_6905.curmodule);
                 gamma = (uu___91_6905.gamma);
                 gamma_cache = (uu___91_6905.gamma_cache);
                 modules = (uu___91_6905.modules);
                 expected_typ = (uu___91_6905.expected_typ);
                 sigtab = (uu___91_6905.sigtab);
                 is_pattern = (uu___91_6905.is_pattern);
                 instantiate_imp = (uu___91_6905.instantiate_imp);
                 effects = (uu___91_6905.effects);
                 generalize = (uu___91_6905.generalize);
                 letrecs = (uu___91_6905.letrecs);
                 top_level = (uu___91_6905.top_level);
                 check_uvars = (uu___91_6905.check_uvars);
                 use_eq = (uu___91_6905.use_eq);
                 is_iface = (uu___91_6905.is_iface);
                 admit = (uu___91_6905.admit);
                 lax = (uu___91_6905.lax);
                 lax_universes = (uu___91_6905.lax_universes);
                 failhard = (uu___91_6905.failhard);
                 nosynth = (uu___91_6905.nosynth);
                 tc_term = (uu___91_6905.tc_term);
                 type_of = (uu___91_6905.type_of);
                 universe_of = (uu___91_6905.universe_of);
                 check_type_of = (uu___91_6905.check_type_of);
                 use_bv_sorts = (uu___91_6905.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___91_6905.proof_ns);
                 synth = (uu___91_6905.synth);
                 is_native_tactic = (uu___91_6905.is_native_tactic);
                 identifier_info = (uu___91_6905.identifier_info);
                 tc_hooks = (uu___91_6905.tc_hooks);
                 dsenv = (uu___91_6905.dsenv);
                 dep_graph = (uu___91_6905.dep_graph)
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
        (let uu___92_6923 = e  in
         {
           solver = (uu___92_6923.solver);
           range = r;
           curmodule = (uu___92_6923.curmodule);
           gamma = (uu___92_6923.gamma);
           gamma_cache = (uu___92_6923.gamma_cache);
           modules = (uu___92_6923.modules);
           expected_typ = (uu___92_6923.expected_typ);
           sigtab = (uu___92_6923.sigtab);
           is_pattern = (uu___92_6923.is_pattern);
           instantiate_imp = (uu___92_6923.instantiate_imp);
           effects = (uu___92_6923.effects);
           generalize = (uu___92_6923.generalize);
           letrecs = (uu___92_6923.letrecs);
           top_level = (uu___92_6923.top_level);
           check_uvars = (uu___92_6923.check_uvars);
           use_eq = (uu___92_6923.use_eq);
           is_iface = (uu___92_6923.is_iface);
           admit = (uu___92_6923.admit);
           lax = (uu___92_6923.lax);
           lax_universes = (uu___92_6923.lax_universes);
           failhard = (uu___92_6923.failhard);
           nosynth = (uu___92_6923.nosynth);
           tc_term = (uu___92_6923.tc_term);
           type_of = (uu___92_6923.type_of);
           universe_of = (uu___92_6923.universe_of);
           check_type_of = (uu___92_6923.check_type_of);
           use_bv_sorts = (uu___92_6923.use_bv_sorts);
           qname_and_index = (uu___92_6923.qname_and_index);
           proof_ns = (uu___92_6923.proof_ns);
           synth = (uu___92_6923.synth);
           is_native_tactic = (uu___92_6923.is_native_tactic);
           identifier_info = (uu___92_6923.identifier_info);
           tc_hooks = (uu___92_6923.tc_hooks);
           dsenv = (uu___92_6923.dsenv);
           dep_graph = (uu___92_6923.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____6933 =
        let uu____6934 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____6934 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6933
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6982 =
          let uu____6983 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6983 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6982
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____7031 =
          let uu____7032 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____7032 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7031
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____7082 =
        let uu____7083 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____7083 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7082
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___93_7136 = env  in
      {
        solver = (uu___93_7136.solver);
        range = (uu___93_7136.range);
        curmodule = lid;
        gamma = (uu___93_7136.gamma);
        gamma_cache = (uu___93_7136.gamma_cache);
        modules = (uu___93_7136.modules);
        expected_typ = (uu___93_7136.expected_typ);
        sigtab = (uu___93_7136.sigtab);
        is_pattern = (uu___93_7136.is_pattern);
        instantiate_imp = (uu___93_7136.instantiate_imp);
        effects = (uu___93_7136.effects);
        generalize = (uu___93_7136.generalize);
        letrecs = (uu___93_7136.letrecs);
        top_level = (uu___93_7136.top_level);
        check_uvars = (uu___93_7136.check_uvars);
        use_eq = (uu___93_7136.use_eq);
        is_iface = (uu___93_7136.is_iface);
        admit = (uu___93_7136.admit);
        lax = (uu___93_7136.lax);
        lax_universes = (uu___93_7136.lax_universes);
        failhard = (uu___93_7136.failhard);
        nosynth = (uu___93_7136.nosynth);
        tc_term = (uu___93_7136.tc_term);
        type_of = (uu___93_7136.type_of);
        universe_of = (uu___93_7136.universe_of);
        check_type_of = (uu___93_7136.check_type_of);
        use_bv_sorts = (uu___93_7136.use_bv_sorts);
        qname_and_index = (uu___93_7136.qname_and_index);
        proof_ns = (uu___93_7136.proof_ns);
        synth = (uu___93_7136.synth);
        is_native_tactic = (uu___93_7136.is_native_tactic);
        identifier_info = (uu___93_7136.identifier_info);
        tc_hooks = (uu___93_7136.tc_hooks);
        dsenv = (uu___93_7136.dsenv);
        dep_graph = (uu___93_7136.dep_graph)
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
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____7162 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7162)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____7170 =
      let uu____7171 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7171  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7170)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____7174  ->
    let uu____7175 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7175
  
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
      | ((formals,t),uu____7213) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7237 = FStar_Syntax_Subst.subst vs t  in (us, uu____7237)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___71_7250  ->
    match uu___71_7250 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7274  -> new_u_univ ()))
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
      let uu____7287 = inst_tscheme t  in
      match uu____7287 with
      | (us,t1) ->
          let uu____7298 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7298)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7310  ->
          match uu____7310 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7325 =
                         let uu____7326 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7327 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7328 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7329 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7326 uu____7327 uu____7328 uu____7329
                          in
                       failwith uu____7325)
                    else ();
                    (let uu____7331 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7331))
               | uu____7338 ->
                   let uu____7339 =
                     let uu____7340 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7340
                      in
                   failwith uu____7339)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____7344 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____7348 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7352 -> false
  
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
             | ([],uu____7386) -> Maybe
             | (uu____7393,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7412 -> No  in
           aux cur1 lns)
        else No
  
let (lookup_qname :
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____7517 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7517 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___72_7562  ->
                   match uu___72_7562 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7605 =
                           let uu____7624 =
                             let uu____7639 = inst_tscheme t  in
                             FStar_Util.Inl uu____7639  in
                           (uu____7624, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7605
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7705,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7707);
                                     FStar_Syntax_Syntax.sigrng = uu____7708;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7709;
                                     FStar_Syntax_Syntax.sigmeta = uu____7710;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7711;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7731 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7731
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7777 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7784 -> cache t  in
                       let uu____7785 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7785 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7860 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7860 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7946 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____8026 = find_in_sigtab env lid  in
         match uu____8026 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8125) ->
          add_sigelts env ses
      | uu____8134 ->
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
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____8148 -> ()))

and (add_sigelts :
  env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit) =
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
        (fun uu___73_8175  ->
           match uu___73_8175 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8193 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____8246,lb::[]),uu____8248) ->
            let uu____8261 =
              let uu____8270 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____8279 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____8270, uu____8279)  in
            FStar_Pervasives_Native.Some uu____8261
        | FStar_Syntax_Syntax.Sig_let ((uu____8292,lbs),uu____8294) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____8330 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____8342 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____8342
                     then
                       let uu____8353 =
                         let uu____8362 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____8371 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____8362, uu____8371)  in
                       FStar_Pervasives_Native.Some uu____8353
                     else FStar_Pervasives_Native.None)
        | uu____8393 -> FStar_Pervasives_Native.None
  
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
          let uu____8446 =
            let uu____8455 =
              let uu____8460 =
                let uu____8461 =
                  let uu____8464 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____8464
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____8461)  in
              inst_tscheme1 uu____8460  in
            (uu____8455, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8446
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____8484,uu____8485) ->
          let uu____8490 =
            let uu____8499 =
              let uu____8504 =
                let uu____8505 =
                  let uu____8508 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____8508  in
                (us, uu____8505)  in
              inst_tscheme1 uu____8504  in
            (uu____8499, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8490
      | uu____8525 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____8603 =
          match uu____8603 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____8699,uvs,t,uu____8702,uu____8703,uu____8704);
                      FStar_Syntax_Syntax.sigrng = uu____8705;
                      FStar_Syntax_Syntax.sigquals = uu____8706;
                      FStar_Syntax_Syntax.sigmeta = uu____8707;
                      FStar_Syntax_Syntax.sigattrs = uu____8708;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8729 =
                     let uu____8738 = inst_tscheme1 (uvs, t)  in
                     (uu____8738, rng)  in
                   FStar_Pervasives_Native.Some uu____8729
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____8758;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____8760;
                      FStar_Syntax_Syntax.sigattrs = uu____8761;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8778 =
                     let uu____8779 = in_cur_mod env l  in uu____8779 = Yes
                      in
                   if uu____8778
                   then
                     let uu____8790 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____8790
                      then
                        let uu____8803 =
                          let uu____8812 = inst_tscheme1 (uvs, t)  in
                          (uu____8812, rng)  in
                        FStar_Pervasives_Native.Some uu____8803
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____8839 =
                        let uu____8848 = inst_tscheme1 (uvs, t)  in
                        (uu____8848, rng)  in
                      FStar_Pervasives_Native.Some uu____8839)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8869,uu____8870);
                      FStar_Syntax_Syntax.sigrng = uu____8871;
                      FStar_Syntax_Syntax.sigquals = uu____8872;
                      FStar_Syntax_Syntax.sigmeta = uu____8873;
                      FStar_Syntax_Syntax.sigattrs = uu____8874;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____8913 =
                          let uu____8922 = inst_tscheme1 (uvs, k)  in
                          (uu____8922, rng)  in
                        FStar_Pervasives_Native.Some uu____8913
                    | uu____8939 ->
                        let uu____8940 =
                          let uu____8949 =
                            let uu____8954 =
                              let uu____8955 =
                                let uu____8958 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8958
                                 in
                              (uvs, uu____8955)  in
                            inst_tscheme1 uu____8954  in
                          (uu____8949, rng)  in
                        FStar_Pervasives_Native.Some uu____8940)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8979,uu____8980);
                      FStar_Syntax_Syntax.sigrng = uu____8981;
                      FStar_Syntax_Syntax.sigquals = uu____8982;
                      FStar_Syntax_Syntax.sigmeta = uu____8983;
                      FStar_Syntax_Syntax.sigattrs = uu____8984;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____9024 =
                          let uu____9033 = inst_tscheme_with (uvs, k) us  in
                          (uu____9033, rng)  in
                        FStar_Pervasives_Native.Some uu____9024
                    | uu____9050 ->
                        let uu____9051 =
                          let uu____9060 =
                            let uu____9065 =
                              let uu____9066 =
                                let uu____9069 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9069
                                 in
                              (uvs, uu____9066)  in
                            inst_tscheme_with uu____9065 us  in
                          (uu____9060, rng)  in
                        FStar_Pervasives_Native.Some uu____9051)
               | FStar_Util.Inr se ->
                   let uu____9103 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____9124;
                          FStar_Syntax_Syntax.sigrng = uu____9125;
                          FStar_Syntax_Syntax.sigquals = uu____9126;
                          FStar_Syntax_Syntax.sigmeta = uu____9127;
                          FStar_Syntax_Syntax.sigattrs = uu____9128;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____9143 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____9103
                     (FStar_Util.map_option
                        (fun uu____9191  ->
                           match uu____9191 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____9222 =
          let uu____9233 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____9233 mapper  in
        match uu____9222 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            FStar_Pervasives_Native.Some
              ((us,
                 (let uu___94_9326 = t  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___94_9326.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                    FStar_Syntax_Syntax.vars =
                      (uu___94_9326.FStar_Syntax_Syntax.vars)
                  })), r)
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____9351 = lookup_qname env l  in
      match uu____9351 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9390 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9438 = try_lookup_bv env bv  in
      match uu____9438 with
      | FStar_Pervasives_Native.None  ->
          let uu____9453 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9453 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9468 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9469 =
            let uu____9470 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9470  in
          (uu____9468, uu____9469)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____9487 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____9487 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9553 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9553  in
          let uu____9554 =
            let uu____9563 =
              let uu____9568 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9568)  in
            (uu____9563, r1)  in
          FStar_Pervasives_Native.Some uu____9554
  
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
        let uu____9596 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____9596 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____9629,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____9654 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____9654  in
            let uu____9655 =
              let uu____9660 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____9660, r1)  in
            FStar_Pervasives_Native.Some uu____9655
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____9679 = try_lookup_lid env l  in
      match uu____9679 with
      | FStar_Pervasives_Native.None  ->
          let uu____9706 = name_not_found l  in
          FStar_Errors.raise_error uu____9706 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___74_9746  ->
              match uu___74_9746 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9748 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9763 = lookup_qname env lid  in
      match uu____9763 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9792,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9795;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9797;
              FStar_Syntax_Syntax.sigattrs = uu____9798;_},FStar_Pervasives_Native.None
            ),uu____9799)
          ->
          let uu____9848 =
            let uu____9859 =
              let uu____9864 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9864)  in
            (uu____9859, q)  in
          FStar_Pervasives_Native.Some uu____9848
      | uu____9881 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9918 = lookup_qname env lid  in
      match uu____9918 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9943,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9946;
              FStar_Syntax_Syntax.sigquals = uu____9947;
              FStar_Syntax_Syntax.sigmeta = uu____9948;
              FStar_Syntax_Syntax.sigattrs = uu____9949;_},FStar_Pervasives_Native.None
            ),uu____9950)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9999 ->
          let uu____10020 = name_not_found lid  in
          FStar_Errors.raise_error uu____10020 (FStar_Ident.range_of_lid lid)
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10039 = lookup_qname env lid  in
      match uu____10039 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10064,uvs,t,uu____10067,uu____10068,uu____10069);
              FStar_Syntax_Syntax.sigrng = uu____10070;
              FStar_Syntax_Syntax.sigquals = uu____10071;
              FStar_Syntax_Syntax.sigmeta = uu____10072;
              FStar_Syntax_Syntax.sigattrs = uu____10073;_},FStar_Pervasives_Native.None
            ),uu____10074)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____10127 ->
          let uu____10148 = name_not_found lid  in
          FStar_Errors.raise_error uu____10148 (FStar_Ident.range_of_lid lid)
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10169 = lookup_qname env lid  in
      match uu____10169 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10196,uu____10197,uu____10198,uu____10199,uu____10200,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10202;
              FStar_Syntax_Syntax.sigquals = uu____10203;
              FStar_Syntax_Syntax.sigmeta = uu____10204;
              FStar_Syntax_Syntax.sigattrs = uu____10205;_},uu____10206),uu____10207)
          -> (true, dcs)
      | uu____10268 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____10297 = lookup_qname env lid  in
      match uu____10297 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10318,uu____10319,uu____10320,l,uu____10322,uu____10323);
              FStar_Syntax_Syntax.sigrng = uu____10324;
              FStar_Syntax_Syntax.sigquals = uu____10325;
              FStar_Syntax_Syntax.sigmeta = uu____10326;
              FStar_Syntax_Syntax.sigattrs = uu____10327;_},uu____10328),uu____10329)
          -> l
      | uu____10384 ->
          let uu____10405 =
            let uu____10406 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10406  in
          failwith uu____10405
  
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
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl))))
           in
        let uu____10440 = lookup_qname env lid  in
        match uu____10440 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10468)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10519,lbs),uu____10521)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10549 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10549
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10581 -> FStar_Pervasives_Native.None)
        | uu____10586 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10625 = lookup_qname env lid  in
      match uu____10625 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____10651),uu____10652) ->
          FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
      | uu____10701 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____10734 = lookup_qname env ftv  in
      match uu____10734 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10758) ->
          let uu____10803 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____10803 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10824,t),r) ->
               let uu____10839 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10839)
      | uu____10840 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____10867 = try_lookup_effect_lid env ftv  in
      match uu____10867 with
      | FStar_Pervasives_Native.None  ->
          let uu____10870 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10870 (FStar_Ident.range_of_lid ftv)
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
        let uu____10891 = lookup_qname env lid0  in
        match uu____10891 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10922);
                FStar_Syntax_Syntax.sigrng = uu____10923;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10925;
                FStar_Syntax_Syntax.sigattrs = uu____10926;_},FStar_Pervasives_Native.None
              ),uu____10927)
            ->
            let lid1 =
              let uu____10981 =
                let uu____10982 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10982
                 in
              FStar_Ident.set_lid_range lid uu____10981  in
            let uu____10983 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___75_10987  ->
                      match uu___75_10987 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10988 -> false))
               in
            if uu____10983
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____11002 =
                      let uu____11003 =
                        let uu____11004 = get_range env  in
                        FStar_Range.string_of_range uu____11004  in
                      let uu____11005 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____11006 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____11003 uu____11005 uu____11006
                       in
                    failwith uu____11002)
                  in
               match (binders, univs1) with
               | ([],uu____11013) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____11030,uu____11031::uu____11032::uu____11033) ->
                   let uu____11038 =
                     let uu____11039 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____11040 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____11039 uu____11040
                      in
                   failwith uu____11038
               | uu____11047 ->
                   let uu____11052 =
                     let uu____11057 =
                       let uu____11058 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____11058)  in
                     inst_tscheme_with uu____11057 insts  in
                   (match uu____11052 with
                    | (uu____11069,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____11072 =
                          let uu____11073 = FStar_Syntax_Subst.compress t1
                             in
                          uu____11073.FStar_Syntax_Syntax.n  in
                        (match uu____11072 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____11120 -> failwith "Impossible")))
        | uu____11127 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____11167 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____11167 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____11180,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____11187 = find1 l2  in
            (match uu____11187 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____11194 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____11194 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____11198 = find1 l  in
            (match uu____11198 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____11212 = lookup_qname env l1  in
      match uu____11212 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____11235;
              FStar_Syntax_Syntax.sigrng = uu____11236;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11238;
              FStar_Syntax_Syntax.sigattrs = uu____11239;_},uu____11240),uu____11241)
          -> q
      | uu____11292 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____11325 =
          let uu____11326 =
            let uu____11327 = FStar_Util.string_of_int i  in
            let uu____11328 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____11327 uu____11328
             in
          failwith uu____11326  in
        let uu____11329 = lookup_datacon env lid  in
        match uu____11329 with
        | (uu____11334,t) ->
            let uu____11336 =
              let uu____11337 = FStar_Syntax_Subst.compress t  in
              uu____11337.FStar_Syntax_Syntax.n  in
            (match uu____11336 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11341) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____11372 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____11372
                      FStar_Pervasives_Native.fst)
             | uu____11381 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11388 = lookup_qname env l  in
      match uu____11388 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11409,uu____11410,uu____11411);
              FStar_Syntax_Syntax.sigrng = uu____11412;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11414;
              FStar_Syntax_Syntax.sigattrs = uu____11415;_},uu____11416),uu____11417)
          ->
          FStar_Util.for_some
            (fun uu___76_11470  ->
               match uu___76_11470 with
               | FStar_Syntax_Syntax.Projector uu____11471 -> true
               | uu____11476 -> false) quals
      | uu____11477 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11504 = lookup_qname env lid  in
      match uu____11504 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11525,uu____11526,uu____11527,uu____11528,uu____11529,uu____11530);
              FStar_Syntax_Syntax.sigrng = uu____11531;
              FStar_Syntax_Syntax.sigquals = uu____11532;
              FStar_Syntax_Syntax.sigmeta = uu____11533;
              FStar_Syntax_Syntax.sigattrs = uu____11534;_},uu____11535),uu____11536)
          -> true
      | uu____11591 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11618 = lookup_qname env lid  in
      match uu____11618 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11639,uu____11640,uu____11641,uu____11642,uu____11643,uu____11644);
              FStar_Syntax_Syntax.sigrng = uu____11645;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11647;
              FStar_Syntax_Syntax.sigattrs = uu____11648;_},uu____11649),uu____11650)
          ->
          FStar_Util.for_some
            (fun uu___77_11711  ->
               match uu___77_11711 with
               | FStar_Syntax_Syntax.RecordType uu____11712 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11721 -> true
               | uu____11730 -> false) quals
      | uu____11731 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11758 = lookup_qname env lid  in
      match uu____11758 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11779,uu____11780);
              FStar_Syntax_Syntax.sigrng = uu____11781;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11783;
              FStar_Syntax_Syntax.sigattrs = uu____11784;_},uu____11785),uu____11786)
          ->
          FStar_Util.for_some
            (fun uu___78_11843  ->
               match uu___78_11843 with
               | FStar_Syntax_Syntax.Action uu____11844 -> true
               | uu____11845 -> false) quals
      | uu____11846 -> false
  
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
      let uu____11876 =
        let uu____11877 = FStar_Syntax_Util.un_uinst head1  in
        uu____11877.FStar_Syntax_Syntax.n  in
      match uu____11876 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11881 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11888 = lookup_qname env l  in
      match uu____11888 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11910),uu____11911) ->
          FStar_Util.for_some
            (fun uu___79_11959  ->
               match uu___79_11959 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11960 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11961 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____12046 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____12062) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____12079 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____12086 ->
                 FStar_Pervasives_Native.Some true
             | uu____12103 -> FStar_Pervasives_Native.Some false)
         in
      let uu____12104 =
        let uu____12107 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____12107 mapper  in
      match uu____12104 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____12153 = lookup_qname env lid  in
      match uu____12153 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12174,uu____12175,tps,uu____12177,uu____12178,uu____12179);
              FStar_Syntax_Syntax.sigrng = uu____12180;
              FStar_Syntax_Syntax.sigquals = uu____12181;
              FStar_Syntax_Syntax.sigmeta = uu____12182;
              FStar_Syntax_Syntax.sigattrs = uu____12183;_},uu____12184),uu____12185)
          -> FStar_List.length tps
      | uu____12248 ->
          let uu____12269 = name_not_found lid  in
          FStar_Errors.raise_error uu____12269 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____12313  ->
              match uu____12313 with
              | (d,uu____12321) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____12332 = effect_decl_opt env l  in
      match uu____12332 with
      | FStar_Pervasives_Native.None  ->
          let uu____12347 = name_not_found l  in
          FStar_Errors.raise_error uu____12347 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____12373  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____12388  ->
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
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid))
          then
            (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____12421 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____12474  ->
                       match uu____12474 with
                       | (m1,m2,uu____12487,uu____12488,uu____12489) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____12421 with
             | FStar_Pervasives_Native.None  ->
                 let uu____12506 =
                   let uu____12511 =
                     let uu____12512 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____12513 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____12512
                       uu____12513
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____12511)
                    in
                 FStar_Errors.raise_error uu____12506 env.range
             | FStar_Pervasives_Native.Some
                 (uu____12520,uu____12521,m3,j1,j2) -> (m3, j1, j2))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
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
  'Auu____12558 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12558)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12585 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12611  ->
                match uu____12611 with
                | (d,uu____12617) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____12585 with
      | FStar_Pervasives_Native.None  ->
          let uu____12628 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12628
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12641 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12641 with
           | (uu____12652,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12662)::(wp,uu____12664)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12700 -> failwith "Impossible"))
  
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
          if
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Parser_Const.effect_GTot_lid
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
                 let uu____12743 = get_range env  in
                 let uu____12744 =
                   let uu____12747 =
                     let uu____12748 =
                       let uu____12763 =
                         let uu____12766 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____12766]  in
                       (null_wp, uu____12763)  in
                     FStar_Syntax_Syntax.Tm_app uu____12748  in
                   FStar_Syntax_Syntax.mk uu____12747  in
                 uu____12744 FStar_Pervasives_Native.None uu____12743  in
               let uu____12772 =
                 let uu____12773 =
                   let uu____12782 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____12782]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12773;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____12772)
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___95_12791 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___95_12791.order);
              joins = (uu___95_12791.joins)
            }  in
          let uu___96_12800 = env  in
          {
            solver = (uu___96_12800.solver);
            range = (uu___96_12800.range);
            curmodule = (uu___96_12800.curmodule);
            gamma = (uu___96_12800.gamma);
            gamma_cache = (uu___96_12800.gamma_cache);
            modules = (uu___96_12800.modules);
            expected_typ = (uu___96_12800.expected_typ);
            sigtab = (uu___96_12800.sigtab);
            is_pattern = (uu___96_12800.is_pattern);
            instantiate_imp = (uu___96_12800.instantiate_imp);
            effects;
            generalize = (uu___96_12800.generalize);
            letrecs = (uu___96_12800.letrecs);
            top_level = (uu___96_12800.top_level);
            check_uvars = (uu___96_12800.check_uvars);
            use_eq = (uu___96_12800.use_eq);
            is_iface = (uu___96_12800.is_iface);
            admit = (uu___96_12800.admit);
            lax = (uu___96_12800.lax);
            lax_universes = (uu___96_12800.lax_universes);
            failhard = (uu___96_12800.failhard);
            nosynth = (uu___96_12800.nosynth);
            tc_term = (uu___96_12800.tc_term);
            type_of = (uu___96_12800.type_of);
            universe_of = (uu___96_12800.universe_of);
            check_type_of = (uu___96_12800.check_type_of);
            use_bv_sorts = (uu___96_12800.use_bv_sorts);
            qname_and_index = (uu___96_12800.qname_and_index);
            proof_ns = (uu___96_12800.proof_ns);
            synth = (uu___96_12800.synth);
            is_native_tactic = (uu___96_12800.is_native_tactic);
            identifier_info = (uu___96_12800.identifier_info);
            tc_hooks = (uu___96_12800.tc_hooks);
            dsenv = (uu___96_12800.dsenv);
            dep_graph = (uu___96_12800.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12820 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12820  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12934 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12935 = l1 u t wp e  in
                                l2 u t uu____12934 uu____12935))
                | uu____12936 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12984 = inst_tscheme_with lift_t [u]  in
            match uu____12984 with
            | (uu____12991,lift_t1) ->
                let uu____12993 =
                  let uu____12996 =
                    let uu____12997 =
                      let uu____13012 =
                        let uu____13015 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____13016 =
                          let uu____13019 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____13019]  in
                        uu____13015 :: uu____13016  in
                      (lift_t1, uu____13012)  in
                    FStar_Syntax_Syntax.Tm_app uu____12997  in
                  FStar_Syntax_Syntax.mk uu____12996  in
                uu____12993 FStar_Pervasives_Native.None
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
            let uu____13069 = inst_tscheme_with lift_t [u]  in
            match uu____13069 with
            | (uu____13076,lift_t1) ->
                let uu____13078 =
                  let uu____13081 =
                    let uu____13082 =
                      let uu____13097 =
                        let uu____13100 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____13101 =
                          let uu____13104 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____13105 =
                            let uu____13108 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____13108]  in
                          uu____13104 :: uu____13105  in
                        uu____13100 :: uu____13101  in
                      (lift_t1, uu____13097)  in
                    FStar_Syntax_Syntax.Tm_app uu____13082  in
                  FStar_Syntax_Syntax.mk uu____13081  in
                uu____13078 FStar_Pervasives_Native.None
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
              let uu____13150 =
                let uu____13151 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____13151
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____13150  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____13155 =
              let uu____13156 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____13156  in
            let uu____13157 =
              let uu____13158 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____13180 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____13180)
                 in
              FStar_Util.dflt "none" uu____13158  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____13155
              uu____13157
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____13206  ->
                    match uu____13206 with
                    | (e,uu____13214) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____13233 =
            match uu____13233 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____13271 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____13292 =
                                       let uu____13301 =
                                         find_edge order1 (i, k)  in
                                       let uu____13304 =
                                         find_edge order1 (k, j)  in
                                       (uu____13301, uu____13304)  in
                                     match uu____13292 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____13319 =
                                           compose_edges e1 e2  in
                                         [uu____13319]
                                     | uu____13320 -> [])))))
                 in
              FStar_List.append order1 uu____13271  in
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
                   let uu____13350 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____13352 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____13352
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____13350
                   then
                     let uu____13357 =
                       let uu____13362 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____13362)
                        in
                     let uu____13363 = get_range env  in
                     FStar_Errors.raise_error uu____13357 uu____13363
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____13488 =
                                              let uu____13497 =
                                                find_edge order2 (i, k)  in
                                              let uu____13500 =
                                                find_edge order2 (j, k)  in
                                              (uu____13497, uu____13500)  in
                                            match uu____13488 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13542,uu____13543)
                                                     ->
                                                     let uu____13550 =
                                                       let uu____13555 =
                                                         let uu____13556 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13556
                                                          in
                                                       let uu____13559 =
                                                         let uu____13560 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13560
                                                          in
                                                       (uu____13555,
                                                         uu____13559)
                                                        in
                                                     (match uu____13550 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
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
                                            | uu____13595 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___97_13668 = env.effects  in
              { decls = (uu___97_13668.decls); order = order2; joins }  in
            let uu___98_13669 = env  in
            {
              solver = (uu___98_13669.solver);
              range = (uu___98_13669.range);
              curmodule = (uu___98_13669.curmodule);
              gamma = (uu___98_13669.gamma);
              gamma_cache = (uu___98_13669.gamma_cache);
              modules = (uu___98_13669.modules);
              expected_typ = (uu___98_13669.expected_typ);
              sigtab = (uu___98_13669.sigtab);
              is_pattern = (uu___98_13669.is_pattern);
              instantiate_imp = (uu___98_13669.instantiate_imp);
              effects;
              generalize = (uu___98_13669.generalize);
              letrecs = (uu___98_13669.letrecs);
              top_level = (uu___98_13669.top_level);
              check_uvars = (uu___98_13669.check_uvars);
              use_eq = (uu___98_13669.use_eq);
              is_iface = (uu___98_13669.is_iface);
              admit = (uu___98_13669.admit);
              lax = (uu___98_13669.lax);
              lax_universes = (uu___98_13669.lax_universes);
              failhard = (uu___98_13669.failhard);
              nosynth = (uu___98_13669.nosynth);
              tc_term = (uu___98_13669.tc_term);
              type_of = (uu___98_13669.type_of);
              universe_of = (uu___98_13669.universe_of);
              check_type_of = (uu___98_13669.check_type_of);
              use_bv_sorts = (uu___98_13669.use_bv_sorts);
              qname_and_index = (uu___98_13669.qname_and_index);
              proof_ns = (uu___98_13669.proof_ns);
              synth = (uu___98_13669.synth);
              is_native_tactic = (uu___98_13669.is_native_tactic);
              identifier_info = (uu___98_13669.identifier_info);
              tc_hooks = (uu___98_13669.tc_hooks);
              dsenv = (uu___98_13669.dsenv);
              dep_graph = (uu___98_13669.dep_graph)
            }))
      | uu____13670 -> env
  
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
        | uu____13694 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13702 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13702 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13719 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13719 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13737 =
                     let uu____13742 =
                       let uu____13743 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13748 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13755 =
                         let uu____13756 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13756  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13743 uu____13748 uu____13755
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13742)
                      in
                   FStar_Errors.raise_error uu____13737
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13761 =
                     let uu____13770 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13770 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13787  ->
                        fun uu____13788  ->
                          match (uu____13787, uu____13788) with
                          | ((x,uu____13810),(t,uu____13812)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13761
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13831 =
                     let uu___99_13832 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___99_13832.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___99_13832.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___99_13832.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___99_13832.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13831
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
          let uu____13854 = effect_decl_opt env effect_name  in
          match uu____13854 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13887 =
                only_reifiable &&
                  (let uu____13889 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13889)
                 in
              if uu____13887
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13905 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13924 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13953 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13953
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13954 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13954
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13964 =
                       let uu____13967 = get_range env  in
                       let uu____13968 =
                         let uu____13971 =
                           let uu____13972 =
                             let uu____13987 =
                               let uu____13990 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13990; wp]  in
                             (repr, uu____13987)  in
                           FStar_Syntax_Syntax.Tm_app uu____13972  in
                         FStar_Syntax_Syntax.mk uu____13971  in
                       uu____13968 FStar_Pervasives_Native.None uu____13967
                        in
                     FStar_Pervasives_Native.Some uu____13964)
  
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
          let uu____14036 =
            let uu____14041 =
              let uu____14042 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____14042
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____14041)  in
          let uu____14043 = get_range env  in
          FStar_Errors.raise_error uu____14036 uu____14043  in
        let uu____14044 = effect_repr_aux true env c u_c  in
        match uu____14044 with
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
      | uu____14078 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____14085 =
        let uu____14086 = FStar_Syntax_Subst.compress t  in
        uu____14086.FStar_Syntax_Syntax.n  in
      match uu____14085 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____14089,c) ->
          is_reifiable_comp env c
      | uu____14107 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____14129)::uu____14130 -> x :: rest
        | (Binding_sig_inst uu____14139)::uu____14140 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____14155 = push1 x rest1  in local :: uu____14155
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___100_14159 = env  in
       let uu____14160 = push1 s env.gamma  in
       {
         solver = (uu___100_14159.solver);
         range = (uu___100_14159.range);
         curmodule = (uu___100_14159.curmodule);
         gamma = uu____14160;
         gamma_cache = (uu___100_14159.gamma_cache);
         modules = (uu___100_14159.modules);
         expected_typ = (uu___100_14159.expected_typ);
         sigtab = (uu___100_14159.sigtab);
         is_pattern = (uu___100_14159.is_pattern);
         instantiate_imp = (uu___100_14159.instantiate_imp);
         effects = (uu___100_14159.effects);
         generalize = (uu___100_14159.generalize);
         letrecs = (uu___100_14159.letrecs);
         top_level = (uu___100_14159.top_level);
         check_uvars = (uu___100_14159.check_uvars);
         use_eq = (uu___100_14159.use_eq);
         is_iface = (uu___100_14159.is_iface);
         admit = (uu___100_14159.admit);
         lax = (uu___100_14159.lax);
         lax_universes = (uu___100_14159.lax_universes);
         failhard = (uu___100_14159.failhard);
         nosynth = (uu___100_14159.nosynth);
         tc_term = (uu___100_14159.tc_term);
         type_of = (uu___100_14159.type_of);
         universe_of = (uu___100_14159.universe_of);
         check_type_of = (uu___100_14159.check_type_of);
         use_bv_sorts = (uu___100_14159.use_bv_sorts);
         qname_and_index = (uu___100_14159.qname_and_index);
         proof_ns = (uu___100_14159.proof_ns);
         synth = (uu___100_14159.synth);
         is_native_tactic = (uu___100_14159.is_native_tactic);
         identifier_info = (uu___100_14159.identifier_info);
         tc_hooks = (uu___100_14159.tc_hooks);
         dsenv = (uu___100_14159.dsenv);
         dep_graph = (uu___100_14159.dep_graph)
       })
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
         in
      build_lattice env1 s
  
let (push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env)
  =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
           in
        build_lattice env1 s
  
let (push_local_binding : env -> binding -> env) =
  fun env  ->
    fun b  ->
      let uu___101_14190 = env  in
      {
        solver = (uu___101_14190.solver);
        range = (uu___101_14190.range);
        curmodule = (uu___101_14190.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___101_14190.gamma_cache);
        modules = (uu___101_14190.modules);
        expected_typ = (uu___101_14190.expected_typ);
        sigtab = (uu___101_14190.sigtab);
        is_pattern = (uu___101_14190.is_pattern);
        instantiate_imp = (uu___101_14190.instantiate_imp);
        effects = (uu___101_14190.effects);
        generalize = (uu___101_14190.generalize);
        letrecs = (uu___101_14190.letrecs);
        top_level = (uu___101_14190.top_level);
        check_uvars = (uu___101_14190.check_uvars);
        use_eq = (uu___101_14190.use_eq);
        is_iface = (uu___101_14190.is_iface);
        admit = (uu___101_14190.admit);
        lax = (uu___101_14190.lax);
        lax_universes = (uu___101_14190.lax_universes);
        failhard = (uu___101_14190.failhard);
        nosynth = (uu___101_14190.nosynth);
        tc_term = (uu___101_14190.tc_term);
        type_of = (uu___101_14190.type_of);
        universe_of = (uu___101_14190.universe_of);
        check_type_of = (uu___101_14190.check_type_of);
        use_bv_sorts = (uu___101_14190.use_bv_sorts);
        qname_and_index = (uu___101_14190.qname_and_index);
        proof_ns = (uu___101_14190.proof_ns);
        synth = (uu___101_14190.synth);
        is_native_tactic = (uu___101_14190.is_native_tactic);
        identifier_info = (uu___101_14190.identifier_info);
        tc_hooks = (uu___101_14190.tc_hooks);
        dsenv = (uu___101_14190.dsenv);
        dep_graph = (uu___101_14190.dep_graph)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___102_14221 = env  in
             {
               solver = (uu___102_14221.solver);
               range = (uu___102_14221.range);
               curmodule = (uu___102_14221.curmodule);
               gamma = rest;
               gamma_cache = (uu___102_14221.gamma_cache);
               modules = (uu___102_14221.modules);
               expected_typ = (uu___102_14221.expected_typ);
               sigtab = (uu___102_14221.sigtab);
               is_pattern = (uu___102_14221.is_pattern);
               instantiate_imp = (uu___102_14221.instantiate_imp);
               effects = (uu___102_14221.effects);
               generalize = (uu___102_14221.generalize);
               letrecs = (uu___102_14221.letrecs);
               top_level = (uu___102_14221.top_level);
               check_uvars = (uu___102_14221.check_uvars);
               use_eq = (uu___102_14221.use_eq);
               is_iface = (uu___102_14221.is_iface);
               admit = (uu___102_14221.admit);
               lax = (uu___102_14221.lax);
               lax_universes = (uu___102_14221.lax_universes);
               failhard = (uu___102_14221.failhard);
               nosynth = (uu___102_14221.nosynth);
               tc_term = (uu___102_14221.tc_term);
               type_of = (uu___102_14221.type_of);
               universe_of = (uu___102_14221.universe_of);
               check_type_of = (uu___102_14221.check_type_of);
               use_bv_sorts = (uu___102_14221.use_bv_sorts);
               qname_and_index = (uu___102_14221.qname_and_index);
               proof_ns = (uu___102_14221.proof_ns);
               synth = (uu___102_14221.synth);
               is_native_tactic = (uu___102_14221.is_native_tactic);
               identifier_info = (uu___102_14221.identifier_info);
               tc_hooks = (uu___102_14221.tc_hooks);
               dsenv = (uu___102_14221.dsenv);
               dep_graph = (uu___102_14221.dep_graph)
             }))
    | uu____14222 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____14244  ->
             match uu____14244 with | (x,uu____14250) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___103_14278 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___103_14278.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___103_14278.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.declarations;
      (let uu___104_14308 = env  in
       {
         solver = (uu___104_14308.solver);
         range = (uu___104_14308.range);
         curmodule = (uu___104_14308.curmodule);
         gamma = [];
         gamma_cache = (uu___104_14308.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___104_14308.sigtab);
         is_pattern = (uu___104_14308.is_pattern);
         instantiate_imp = (uu___104_14308.instantiate_imp);
         effects = (uu___104_14308.effects);
         generalize = (uu___104_14308.generalize);
         letrecs = (uu___104_14308.letrecs);
         top_level = (uu___104_14308.top_level);
         check_uvars = (uu___104_14308.check_uvars);
         use_eq = (uu___104_14308.use_eq);
         is_iface = (uu___104_14308.is_iface);
         admit = (uu___104_14308.admit);
         lax = (uu___104_14308.lax);
         lax_universes = (uu___104_14308.lax_universes);
         failhard = (uu___104_14308.failhard);
         nosynth = (uu___104_14308.nosynth);
         tc_term = (uu___104_14308.tc_term);
         type_of = (uu___104_14308.type_of);
         universe_of = (uu___104_14308.universe_of);
         check_type_of = (uu___104_14308.check_type_of);
         use_bv_sorts = (uu___104_14308.use_bv_sorts);
         qname_and_index = (uu___104_14308.qname_and_index);
         proof_ns = (uu___104_14308.proof_ns);
         synth = (uu___104_14308.synth);
         is_native_tactic = (uu___104_14308.is_native_tactic);
         identifier_info = (uu___104_14308.identifier_info);
         tc_hooks = (uu___104_14308.tc_hooks);
         dsenv = (uu___104_14308.dsenv);
         dep_graph = (uu___104_14308.dep_graph)
       })
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
  
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
        let uu____14340 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____14340 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____14368 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____14368)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___105_14381 = env  in
      {
        solver = (uu___105_14381.solver);
        range = (uu___105_14381.range);
        curmodule = (uu___105_14381.curmodule);
        gamma = (uu___105_14381.gamma);
        gamma_cache = (uu___105_14381.gamma_cache);
        modules = (uu___105_14381.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___105_14381.sigtab);
        is_pattern = (uu___105_14381.is_pattern);
        instantiate_imp = (uu___105_14381.instantiate_imp);
        effects = (uu___105_14381.effects);
        generalize = (uu___105_14381.generalize);
        letrecs = (uu___105_14381.letrecs);
        top_level = (uu___105_14381.top_level);
        check_uvars = (uu___105_14381.check_uvars);
        use_eq = false;
        is_iface = (uu___105_14381.is_iface);
        admit = (uu___105_14381.admit);
        lax = (uu___105_14381.lax);
        lax_universes = (uu___105_14381.lax_universes);
        failhard = (uu___105_14381.failhard);
        nosynth = (uu___105_14381.nosynth);
        tc_term = (uu___105_14381.tc_term);
        type_of = (uu___105_14381.type_of);
        universe_of = (uu___105_14381.universe_of);
        check_type_of = (uu___105_14381.check_type_of);
        use_bv_sorts = (uu___105_14381.use_bv_sorts);
        qname_and_index = (uu___105_14381.qname_and_index);
        proof_ns = (uu___105_14381.proof_ns);
        synth = (uu___105_14381.synth);
        is_native_tactic = (uu___105_14381.is_native_tactic);
        identifier_info = (uu___105_14381.identifier_info);
        tc_hooks = (uu___105_14381.tc_hooks);
        dsenv = (uu___105_14381.dsenv);
        dep_graph = (uu___105_14381.dep_graph)
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
    let uu____14405 = expected_typ env_  in
    ((let uu___106_14411 = env_  in
      {
        solver = (uu___106_14411.solver);
        range = (uu___106_14411.range);
        curmodule = (uu___106_14411.curmodule);
        gamma = (uu___106_14411.gamma);
        gamma_cache = (uu___106_14411.gamma_cache);
        modules = (uu___106_14411.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___106_14411.sigtab);
        is_pattern = (uu___106_14411.is_pattern);
        instantiate_imp = (uu___106_14411.instantiate_imp);
        effects = (uu___106_14411.effects);
        generalize = (uu___106_14411.generalize);
        letrecs = (uu___106_14411.letrecs);
        top_level = (uu___106_14411.top_level);
        check_uvars = (uu___106_14411.check_uvars);
        use_eq = false;
        is_iface = (uu___106_14411.is_iface);
        admit = (uu___106_14411.admit);
        lax = (uu___106_14411.lax);
        lax_universes = (uu___106_14411.lax_universes);
        failhard = (uu___106_14411.failhard);
        nosynth = (uu___106_14411.nosynth);
        tc_term = (uu___106_14411.tc_term);
        type_of = (uu___106_14411.type_of);
        universe_of = (uu___106_14411.universe_of);
        check_type_of = (uu___106_14411.check_type_of);
        use_bv_sorts = (uu___106_14411.use_bv_sorts);
        qname_and_index = (uu___106_14411.qname_and_index);
        proof_ns = (uu___106_14411.proof_ns);
        synth = (uu___106_14411.synth);
        is_native_tactic = (uu___106_14411.is_native_tactic);
        identifier_info = (uu___106_14411.identifier_info);
        tc_hooks = (uu___106_14411.tc_hooks);
        dsenv = (uu___106_14411.dsenv);
        dep_graph = (uu___106_14411.dep_graph)
      }), uu____14405)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____14424 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___80_14434  ->
                    match uu___80_14434 with
                    | Binding_sig (uu____14437,se) -> [se]
                    | uu____14443 -> []))
             in
          FStar_All.pipe_right uu____14424 FStar_List.rev
        else m.FStar_Syntax_Syntax.declarations  in
      add_sigelts env sigs;
      (let uu___107_14450 = env  in
       {
         solver = (uu___107_14450.solver);
         range = (uu___107_14450.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___107_14450.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___107_14450.expected_typ);
         sigtab = (uu___107_14450.sigtab);
         is_pattern = (uu___107_14450.is_pattern);
         instantiate_imp = (uu___107_14450.instantiate_imp);
         effects = (uu___107_14450.effects);
         generalize = (uu___107_14450.generalize);
         letrecs = (uu___107_14450.letrecs);
         top_level = (uu___107_14450.top_level);
         check_uvars = (uu___107_14450.check_uvars);
         use_eq = (uu___107_14450.use_eq);
         is_iface = (uu___107_14450.is_iface);
         admit = (uu___107_14450.admit);
         lax = (uu___107_14450.lax);
         lax_universes = (uu___107_14450.lax_universes);
         failhard = (uu___107_14450.failhard);
         nosynth = (uu___107_14450.nosynth);
         tc_term = (uu___107_14450.tc_term);
         type_of = (uu___107_14450.type_of);
         universe_of = (uu___107_14450.universe_of);
         check_type_of = (uu___107_14450.check_type_of);
         use_bv_sorts = (uu___107_14450.use_bv_sorts);
         qname_and_index = (uu___107_14450.qname_and_index);
         proof_ns = (uu___107_14450.proof_ns);
         synth = (uu___107_14450.synth);
         is_native_tactic = (uu___107_14450.is_native_tactic);
         identifier_info = (uu___107_14450.identifier_info);
         tc_hooks = (uu___107_14450.tc_hooks);
         dsenv = (uu___107_14450.dsenv);
         dep_graph = (uu___107_14450.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14531)::tl1 -> aux out tl1
      | (Binding_lid (uu____14535,(uu____14536,t)))::tl1 ->
          let uu____14551 =
            let uu____14558 = FStar_Syntax_Free.uvars t  in
            ext out uu____14558  in
          aux uu____14551 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14565;
            FStar_Syntax_Syntax.index = uu____14566;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14573 =
            let uu____14580 = FStar_Syntax_Free.uvars t  in
            ext out uu____14580  in
          aux uu____14573 tl1
      | (Binding_sig uu____14587)::uu____14588 -> out
      | (Binding_sig_inst uu____14597)::uu____14598 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14653)::tl1 -> aux out tl1
      | (Binding_univ uu____14665)::tl1 -> aux out tl1
      | (Binding_lid (uu____14669,(uu____14670,t)))::tl1 ->
          let uu____14685 =
            let uu____14688 = FStar_Syntax_Free.univs t  in
            ext out uu____14688  in
          aux uu____14685 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14691;
            FStar_Syntax_Syntax.index = uu____14692;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14699 =
            let uu____14702 = FStar_Syntax_Free.univs t  in
            ext out uu____14702  in
          aux uu____14699 tl1
      | (Binding_sig uu____14705)::uu____14706 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14759)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14775 = FStar_Util.fifo_set_add uname out  in
          aux uu____14775 tl1
      | (Binding_lid (uu____14778,(uu____14779,t)))::tl1 ->
          let uu____14794 =
            let uu____14797 = FStar_Syntax_Free.univnames t  in
            ext out uu____14797  in
          aux uu____14794 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14800;
            FStar_Syntax_Syntax.index = uu____14801;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14808 =
            let uu____14811 = FStar_Syntax_Free.univnames t  in
            ext out uu____14811  in
          aux uu____14808 tl1
      | (Binding_sig uu____14814)::uu____14815 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___81_14839  ->
            match uu___81_14839 with
            | Binding_var x -> [x]
            | Binding_lid uu____14843 -> []
            | Binding_sig uu____14848 -> []
            | Binding_univ uu____14855 -> []
            | Binding_sig_inst uu____14856 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____14872 =
      let uu____14875 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14875
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14872 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____14897 =
      let uu____14898 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___82_14908  ->
                match uu___82_14908 with
                | Binding_var x ->
                    let uu____14910 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14910
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14913) ->
                    let uu____14914 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14914
                | Binding_sig (ls,uu____14916) ->
                    let uu____14921 =
                      let uu____14922 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14922
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14921
                | Binding_sig_inst (ls,uu____14932,uu____14933) ->
                    let uu____14938 =
                      let uu____14939 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14939
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14938))
         in
      FStar_All.pipe_right uu____14898 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14897 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____14956 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14956
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14984  ->
                 fun uu____14985  ->
                   match (uu____14984, uu____14985) with
                   | ((b1,uu____15003),(b2,uu____15005)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___83_15047  ->
    match uu___83_15047 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____15048 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___84_15066  ->
             match uu___84_15066 with
             | Binding_sig (lids,uu____15072) -> FStar_List.append lids keys
             | uu____15077 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____15083  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____15117) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____15136,uu____15137) -> false  in
      let uu____15146 =
        FStar_List.tryFind
          (fun uu____15164  ->
             match uu____15164 with | (p,uu____15172) -> list_prefix p path)
          env.proof_ns
         in
      match uu____15146 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____15183,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15201 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____15201
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___108_15213 = e  in
        {
          solver = (uu___108_15213.solver);
          range = (uu___108_15213.range);
          curmodule = (uu___108_15213.curmodule);
          gamma = (uu___108_15213.gamma);
          gamma_cache = (uu___108_15213.gamma_cache);
          modules = (uu___108_15213.modules);
          expected_typ = (uu___108_15213.expected_typ);
          sigtab = (uu___108_15213.sigtab);
          is_pattern = (uu___108_15213.is_pattern);
          instantiate_imp = (uu___108_15213.instantiate_imp);
          effects = (uu___108_15213.effects);
          generalize = (uu___108_15213.generalize);
          letrecs = (uu___108_15213.letrecs);
          top_level = (uu___108_15213.top_level);
          check_uvars = (uu___108_15213.check_uvars);
          use_eq = (uu___108_15213.use_eq);
          is_iface = (uu___108_15213.is_iface);
          admit = (uu___108_15213.admit);
          lax = (uu___108_15213.lax);
          lax_universes = (uu___108_15213.lax_universes);
          failhard = (uu___108_15213.failhard);
          nosynth = (uu___108_15213.nosynth);
          tc_term = (uu___108_15213.tc_term);
          type_of = (uu___108_15213.type_of);
          universe_of = (uu___108_15213.universe_of);
          check_type_of = (uu___108_15213.check_type_of);
          use_bv_sorts = (uu___108_15213.use_bv_sorts);
          qname_and_index = (uu___108_15213.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___108_15213.synth);
          is_native_tactic = (uu___108_15213.is_native_tactic);
          identifier_info = (uu___108_15213.identifier_info);
          tc_hooks = (uu___108_15213.tc_hooks);
          dsenv = (uu___108_15213.dsenv);
          dep_graph = (uu___108_15213.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___109_15239 = e  in
      {
        solver = (uu___109_15239.solver);
        range = (uu___109_15239.range);
        curmodule = (uu___109_15239.curmodule);
        gamma = (uu___109_15239.gamma);
        gamma_cache = (uu___109_15239.gamma_cache);
        modules = (uu___109_15239.modules);
        expected_typ = (uu___109_15239.expected_typ);
        sigtab = (uu___109_15239.sigtab);
        is_pattern = (uu___109_15239.is_pattern);
        instantiate_imp = (uu___109_15239.instantiate_imp);
        effects = (uu___109_15239.effects);
        generalize = (uu___109_15239.generalize);
        letrecs = (uu___109_15239.letrecs);
        top_level = (uu___109_15239.top_level);
        check_uvars = (uu___109_15239.check_uvars);
        use_eq = (uu___109_15239.use_eq);
        is_iface = (uu___109_15239.is_iface);
        admit = (uu___109_15239.admit);
        lax = (uu___109_15239.lax);
        lax_universes = (uu___109_15239.lax_universes);
        failhard = (uu___109_15239.failhard);
        nosynth = (uu___109_15239.nosynth);
        tc_term = (uu___109_15239.tc_term);
        type_of = (uu___109_15239.type_of);
        universe_of = (uu___109_15239.universe_of);
        check_type_of = (uu___109_15239.check_type_of);
        use_bv_sorts = (uu___109_15239.use_bv_sorts);
        qname_and_index = (uu___109_15239.qname_and_index);
        proof_ns = ns;
        synth = (uu___109_15239.synth);
        is_native_tactic = (uu___109_15239.is_native_tactic);
        identifier_info = (uu___109_15239.identifier_info);
        tc_hooks = (uu___109_15239.tc_hooks);
        dsenv = (uu___109_15239.dsenv);
        dep_graph = (uu___109_15239.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____15250 = FStar_Syntax_Free.names t  in
      let uu____15253 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____15250 uu____15253
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____15270 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____15270
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____15276 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____15276
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____15291 =
      match uu____15291 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____15307 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____15307)
       in
    let uu____15309 =
      let uu____15312 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____15312 FStar_List.rev  in
    FStar_All.pipe_right uu____15309 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____15329  -> ());
    push = (fun uu____15331  -> ());
    pop = (fun uu____15333  -> ());
    encode_modul = (fun uu____15336  -> fun uu____15337  -> ());
    encode_sig = (fun uu____15340  -> fun uu____15341  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____15347 =
             let uu____15354 = FStar_Options.peek ()  in (e, g, uu____15354)
              in
           [uu____15347]);
    solve = (fun uu____15370  -> fun uu____15371  -> fun uu____15372  -> ());
    finish = (fun uu____15378  -> ());
    refresh = (fun uu____15380  -> ())
  } 