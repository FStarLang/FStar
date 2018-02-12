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
           (fun uu___70_5525  ->
              match uu___70_5525 with
              | Binding_var x ->
                  let y =
                    let uu____5528 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____5528  in
                  let uu____5529 =
                    let uu____5530 = FStar_Syntax_Subst.compress y  in
                    uu____5530.FStar_Syntax_Syntax.n  in
                  (match uu____5529 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5534 =
                         let uu___85_5535 = y1  in
                         let uu____5536 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___85_5535.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___85_5535.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5536
                         }  in
                       Binding_var uu____5534
                   | uu____5539 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___86_5547 = env  in
      let uu____5548 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___86_5547.solver);
        range = (uu___86_5547.range);
        curmodule = (uu___86_5547.curmodule);
        gamma = uu____5548;
        gamma_cache = (uu___86_5547.gamma_cache);
        modules = (uu___86_5547.modules);
        expected_typ = (uu___86_5547.expected_typ);
        sigtab = (uu___86_5547.sigtab);
        is_pattern = (uu___86_5547.is_pattern);
        instantiate_imp = (uu___86_5547.instantiate_imp);
        effects = (uu___86_5547.effects);
        generalize = (uu___86_5547.generalize);
        letrecs = (uu___86_5547.letrecs);
        top_level = (uu___86_5547.top_level);
        check_uvars = (uu___86_5547.check_uvars);
        use_eq = (uu___86_5547.use_eq);
        is_iface = (uu___86_5547.is_iface);
        admit = (uu___86_5547.admit);
        lax = (uu___86_5547.lax);
        lax_universes = (uu___86_5547.lax_universes);
        failhard = (uu___86_5547.failhard);
        nosynth = (uu___86_5547.nosynth);
        tc_term = (uu___86_5547.tc_term);
        type_of = (uu___86_5547.type_of);
        universe_of = (uu___86_5547.universe_of);
        check_type_of = (uu___86_5547.check_type_of);
        use_bv_sorts = (uu___86_5547.use_bv_sorts);
        qname_and_index = (uu___86_5547.qname_and_index);
        proof_ns = (uu___86_5547.proof_ns);
        synth = (uu___86_5547.synth);
        is_native_tactic = (uu___86_5547.is_native_tactic);
        identifier_info = (uu___86_5547.identifier_info);
        tc_hooks = (uu___86_5547.tc_hooks);
        dsenv = (uu___86_5547.dsenv);
        dep_graph = (uu___86_5547.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____5555  -> fun uu____5556  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___87_5566 = env  in
      {
        solver = (uu___87_5566.solver);
        range = (uu___87_5566.range);
        curmodule = (uu___87_5566.curmodule);
        gamma = (uu___87_5566.gamma);
        gamma_cache = (uu___87_5566.gamma_cache);
        modules = (uu___87_5566.modules);
        expected_typ = (uu___87_5566.expected_typ);
        sigtab = (uu___87_5566.sigtab);
        is_pattern = (uu___87_5566.is_pattern);
        instantiate_imp = (uu___87_5566.instantiate_imp);
        effects = (uu___87_5566.effects);
        generalize = (uu___87_5566.generalize);
        letrecs = (uu___87_5566.letrecs);
        top_level = (uu___87_5566.top_level);
        check_uvars = (uu___87_5566.check_uvars);
        use_eq = (uu___87_5566.use_eq);
        is_iface = (uu___87_5566.is_iface);
        admit = (uu___87_5566.admit);
        lax = (uu___87_5566.lax);
        lax_universes = (uu___87_5566.lax_universes);
        failhard = (uu___87_5566.failhard);
        nosynth = (uu___87_5566.nosynth);
        tc_term = (uu___87_5566.tc_term);
        type_of = (uu___87_5566.type_of);
        universe_of = (uu___87_5566.universe_of);
        check_type_of = (uu___87_5566.check_type_of);
        use_bv_sorts = (uu___87_5566.use_bv_sorts);
        qname_and_index = (uu___87_5566.qname_and_index);
        proof_ns = (uu___87_5566.proof_ns);
        synth = (uu___87_5566.synth);
        is_native_tactic = (uu___87_5566.is_native_tactic);
        identifier_info = (uu___87_5566.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___87_5566.dsenv);
        dep_graph = (uu___87_5566.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___88_5573 = e  in
      {
        solver = (uu___88_5573.solver);
        range = (uu___88_5573.range);
        curmodule = (uu___88_5573.curmodule);
        gamma = (uu___88_5573.gamma);
        gamma_cache = (uu___88_5573.gamma_cache);
        modules = (uu___88_5573.modules);
        expected_typ = (uu___88_5573.expected_typ);
        sigtab = (uu___88_5573.sigtab);
        is_pattern = (uu___88_5573.is_pattern);
        instantiate_imp = (uu___88_5573.instantiate_imp);
        effects = (uu___88_5573.effects);
        generalize = (uu___88_5573.generalize);
        letrecs = (uu___88_5573.letrecs);
        top_level = (uu___88_5573.top_level);
        check_uvars = (uu___88_5573.check_uvars);
        use_eq = (uu___88_5573.use_eq);
        is_iface = (uu___88_5573.is_iface);
        admit = (uu___88_5573.admit);
        lax = (uu___88_5573.lax);
        lax_universes = (uu___88_5573.lax_universes);
        failhard = (uu___88_5573.failhard);
        nosynth = (uu___88_5573.nosynth);
        tc_term = (uu___88_5573.tc_term);
        type_of = (uu___88_5573.type_of);
        universe_of = (uu___88_5573.universe_of);
        check_type_of = (uu___88_5573.check_type_of);
        use_bv_sorts = (uu___88_5573.use_bv_sorts);
        qname_and_index = (uu___88_5573.qname_and_index);
        proof_ns = (uu___88_5573.proof_ns);
        synth = (uu___88_5573.synth);
        is_native_tactic = (uu___88_5573.is_native_tactic);
        identifier_info = (uu___88_5573.identifier_info);
        tc_hooks = (uu___88_5573.tc_hooks);
        dsenv = (uu___88_5573.dsenv);
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
      | (NoDelta ,uu____5588) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5589,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5590,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5591 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____5598 . Prims.unit -> 'Auu____5598 FStar_Util.smap =
  fun uu____5604  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____5607 . Prims.unit -> 'Auu____5607 FStar_Util.smap =
  fun uu____5613  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____5709 = new_gamma_cache ()  in
                let uu____5712 = new_sigtab ()  in
                let uu____5715 = FStar_Options.using_facts_from ()  in
                let uu____5716 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____5719 = FStar_ToSyntax_Env.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____5709;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____5712;
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
                  proof_ns = uu____5715;
                  synth =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  is_native_tactic = (fun uu____5753  -> false);
                  identifier_info = uu____5716;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____5719;
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
  fun uu____5833  ->
    let uu____5834 = FStar_ST.op_Bang query_indices  in
    match uu____5834 with
    | [] -> failwith "Empty query indices!"
    | uu____5884 ->
        let uu____5893 =
          let uu____5902 =
            let uu____5909 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____5909  in
          let uu____5959 = FStar_ST.op_Bang query_indices  in uu____5902 ::
            uu____5959
           in
        FStar_ST.op_Colon_Equals query_indices uu____5893
  
let (pop_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6046  ->
    let uu____6047 = FStar_ST.op_Bang query_indices  in
    match uu____6047 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____6160  ->
    match uu____6160 with
    | (l,n1) ->
        let uu____6167 = FStar_ST.op_Bang query_indices  in
        (match uu____6167 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6278 -> failwith "Empty query indices")
  
let (peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6295  ->
    let uu____6296 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6296
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____6367 =
       let uu____6370 = FStar_ST.op_Bang stack  in env :: uu____6370  in
     FStar_ST.op_Colon_Equals stack uu____6367);
    (let uu___89_6419 = env  in
     let uu____6420 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6423 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6426 =
       let uu____6429 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6429  in
     {
       solver = (uu___89_6419.solver);
       range = (uu___89_6419.range);
       curmodule = (uu___89_6419.curmodule);
       gamma = (uu___89_6419.gamma);
       gamma_cache = uu____6420;
       modules = (uu___89_6419.modules);
       expected_typ = (uu___89_6419.expected_typ);
       sigtab = uu____6423;
       is_pattern = (uu___89_6419.is_pattern);
       instantiate_imp = (uu___89_6419.instantiate_imp);
       effects = (uu___89_6419.effects);
       generalize = (uu___89_6419.generalize);
       letrecs = (uu___89_6419.letrecs);
       top_level = (uu___89_6419.top_level);
       check_uvars = (uu___89_6419.check_uvars);
       use_eq = (uu___89_6419.use_eq);
       is_iface = (uu___89_6419.is_iface);
       admit = (uu___89_6419.admit);
       lax = (uu___89_6419.lax);
       lax_universes = (uu___89_6419.lax_universes);
       failhard = (uu___89_6419.failhard);
       nosynth = (uu___89_6419.nosynth);
       tc_term = (uu___89_6419.tc_term);
       type_of = (uu___89_6419.type_of);
       universe_of = (uu___89_6419.universe_of);
       check_type_of = (uu___89_6419.check_type_of);
       use_bv_sorts = (uu___89_6419.use_bv_sorts);
       qname_and_index = (uu___89_6419.qname_and_index);
       proof_ns = (uu___89_6419.proof_ns);
       synth = (uu___89_6419.synth);
       is_native_tactic = (uu___89_6419.is_native_tactic);
       identifier_info = uu____6426;
       tc_hooks = (uu___89_6419.tc_hooks);
       dsenv = (uu___89_6419.dsenv);
       dep_graph = (uu___89_6419.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____6473  ->
    let uu____6474 = FStar_ST.op_Bang stack  in
    match uu____6474 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6528 -> failwith "Impossible: Too many pops"
  
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
        let uu____6567 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6593  ->
                  match uu____6593 with
                  | (m,uu____6599) -> FStar_Ident.lid_equals l m))
           in
        (match uu____6567 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___90_6606 = env  in
               {
                 solver = (uu___90_6606.solver);
                 range = (uu___90_6606.range);
                 curmodule = (uu___90_6606.curmodule);
                 gamma = (uu___90_6606.gamma);
                 gamma_cache = (uu___90_6606.gamma_cache);
                 modules = (uu___90_6606.modules);
                 expected_typ = (uu___90_6606.expected_typ);
                 sigtab = (uu___90_6606.sigtab);
                 is_pattern = (uu___90_6606.is_pattern);
                 instantiate_imp = (uu___90_6606.instantiate_imp);
                 effects = (uu___90_6606.effects);
                 generalize = (uu___90_6606.generalize);
                 letrecs = (uu___90_6606.letrecs);
                 top_level = (uu___90_6606.top_level);
                 check_uvars = (uu___90_6606.check_uvars);
                 use_eq = (uu___90_6606.use_eq);
                 is_iface = (uu___90_6606.is_iface);
                 admit = (uu___90_6606.admit);
                 lax = (uu___90_6606.lax);
                 lax_universes = (uu___90_6606.lax_universes);
                 failhard = (uu___90_6606.failhard);
                 nosynth = (uu___90_6606.nosynth);
                 tc_term = (uu___90_6606.tc_term);
                 type_of = (uu___90_6606.type_of);
                 universe_of = (uu___90_6606.universe_of);
                 check_type_of = (uu___90_6606.check_type_of);
                 use_bv_sorts = (uu___90_6606.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___90_6606.proof_ns);
                 synth = (uu___90_6606.synth);
                 is_native_tactic = (uu___90_6606.is_native_tactic);
                 identifier_info = (uu___90_6606.identifier_info);
                 tc_hooks = (uu___90_6606.tc_hooks);
                 dsenv = (uu___90_6606.dsenv);
                 dep_graph = (uu___90_6606.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6611,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___91_6619 = env  in
               {
                 solver = (uu___91_6619.solver);
                 range = (uu___91_6619.range);
                 curmodule = (uu___91_6619.curmodule);
                 gamma = (uu___91_6619.gamma);
                 gamma_cache = (uu___91_6619.gamma_cache);
                 modules = (uu___91_6619.modules);
                 expected_typ = (uu___91_6619.expected_typ);
                 sigtab = (uu___91_6619.sigtab);
                 is_pattern = (uu___91_6619.is_pattern);
                 instantiate_imp = (uu___91_6619.instantiate_imp);
                 effects = (uu___91_6619.effects);
                 generalize = (uu___91_6619.generalize);
                 letrecs = (uu___91_6619.letrecs);
                 top_level = (uu___91_6619.top_level);
                 check_uvars = (uu___91_6619.check_uvars);
                 use_eq = (uu___91_6619.use_eq);
                 is_iface = (uu___91_6619.is_iface);
                 admit = (uu___91_6619.admit);
                 lax = (uu___91_6619.lax);
                 lax_universes = (uu___91_6619.lax_universes);
                 failhard = (uu___91_6619.failhard);
                 nosynth = (uu___91_6619.nosynth);
                 tc_term = (uu___91_6619.tc_term);
                 type_of = (uu___91_6619.type_of);
                 universe_of = (uu___91_6619.universe_of);
                 check_type_of = (uu___91_6619.check_type_of);
                 use_bv_sorts = (uu___91_6619.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___91_6619.proof_ns);
                 synth = (uu___91_6619.synth);
                 is_native_tactic = (uu___91_6619.is_native_tactic);
                 identifier_info = (uu___91_6619.identifier_info);
                 tc_hooks = (uu___91_6619.tc_hooks);
                 dsenv = (uu___91_6619.dsenv);
                 dep_graph = (uu___91_6619.dep_graph)
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
        (let uu___92_6637 = e  in
         {
           solver = (uu___92_6637.solver);
           range = r;
           curmodule = (uu___92_6637.curmodule);
           gamma = (uu___92_6637.gamma);
           gamma_cache = (uu___92_6637.gamma_cache);
           modules = (uu___92_6637.modules);
           expected_typ = (uu___92_6637.expected_typ);
           sigtab = (uu___92_6637.sigtab);
           is_pattern = (uu___92_6637.is_pattern);
           instantiate_imp = (uu___92_6637.instantiate_imp);
           effects = (uu___92_6637.effects);
           generalize = (uu___92_6637.generalize);
           letrecs = (uu___92_6637.letrecs);
           top_level = (uu___92_6637.top_level);
           check_uvars = (uu___92_6637.check_uvars);
           use_eq = (uu___92_6637.use_eq);
           is_iface = (uu___92_6637.is_iface);
           admit = (uu___92_6637.admit);
           lax = (uu___92_6637.lax);
           lax_universes = (uu___92_6637.lax_universes);
           failhard = (uu___92_6637.failhard);
           nosynth = (uu___92_6637.nosynth);
           tc_term = (uu___92_6637.tc_term);
           type_of = (uu___92_6637.type_of);
           universe_of = (uu___92_6637.universe_of);
           check_type_of = (uu___92_6637.check_type_of);
           use_bv_sorts = (uu___92_6637.use_bv_sorts);
           qname_and_index = (uu___92_6637.qname_and_index);
           proof_ns = (uu___92_6637.proof_ns);
           synth = (uu___92_6637.synth);
           is_native_tactic = (uu___92_6637.is_native_tactic);
           identifier_info = (uu___92_6637.identifier_info);
           tc_hooks = (uu___92_6637.tc_hooks);
           dsenv = (uu___92_6637.dsenv);
           dep_graph = (uu___92_6637.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____6647 =
        let uu____6648 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____6648 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6647
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6696 =
          let uu____6697 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6697 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6696
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6745 =
          let uu____6746 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6746 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6745
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____6796 =
        let uu____6797 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____6797 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6796
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___93_6850 = env  in
      {
        solver = (uu___93_6850.solver);
        range = (uu___93_6850.range);
        curmodule = lid;
        gamma = (uu___93_6850.gamma);
        gamma_cache = (uu___93_6850.gamma_cache);
        modules = (uu___93_6850.modules);
        expected_typ = (uu___93_6850.expected_typ);
        sigtab = (uu___93_6850.sigtab);
        is_pattern = (uu___93_6850.is_pattern);
        instantiate_imp = (uu___93_6850.instantiate_imp);
        effects = (uu___93_6850.effects);
        generalize = (uu___93_6850.generalize);
        letrecs = (uu___93_6850.letrecs);
        top_level = (uu___93_6850.top_level);
        check_uvars = (uu___93_6850.check_uvars);
        use_eq = (uu___93_6850.use_eq);
        is_iface = (uu___93_6850.is_iface);
        admit = (uu___93_6850.admit);
        lax = (uu___93_6850.lax);
        lax_universes = (uu___93_6850.lax_universes);
        failhard = (uu___93_6850.failhard);
        nosynth = (uu___93_6850.nosynth);
        tc_term = (uu___93_6850.tc_term);
        type_of = (uu___93_6850.type_of);
        universe_of = (uu___93_6850.universe_of);
        check_type_of = (uu___93_6850.check_type_of);
        use_bv_sorts = (uu___93_6850.use_bv_sorts);
        qname_and_index = (uu___93_6850.qname_and_index);
        proof_ns = (uu___93_6850.proof_ns);
        synth = (uu___93_6850.synth);
        is_native_tactic = (uu___93_6850.is_native_tactic);
        identifier_info = (uu___93_6850.identifier_info);
        tc_hooks = (uu___93_6850.tc_hooks);
        dsenv = (uu___93_6850.dsenv);
        dep_graph = (uu___93_6850.dep_graph)
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
    let uu____6876 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____6876)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____6884 =
      let uu____6885 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____6885  in
    (FStar_Errors.Fatal_VariableNotFound, uu____6884)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____6888  ->
    let uu____6889 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____6889
  
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
      | ((formals,t),uu____6927) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____6951 = FStar_Syntax_Subst.subst vs t  in (us, uu____6951)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___71_6964  ->
    match uu___71_6964 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6988  -> new_u_univ ()))
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
      let uu____7001 = inst_tscheme t  in
      match uu____7001 with
      | (us,t1) ->
          let uu____7012 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7012)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7024  ->
          match uu____7024 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7039 =
                         let uu____7040 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7041 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7042 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7043 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7040 uu____7041 uu____7042 uu____7043
                          in
                       failwith uu____7039)
                    else ();
                    (let uu____7045 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7045))
               | uu____7052 ->
                   let uu____7053 =
                     let uu____7054 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7054
                      in
                   failwith uu____7053)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____7058 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____7062 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7066 -> false
  
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
             | ([],uu____7100) -> Maybe
             | (uu____7107,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7126 -> No  in
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
          let uu____7211 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7211 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___72_7256  ->
                   match uu___72_7256 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7299 =
                           let uu____7318 =
                             let uu____7333 = inst_tscheme t  in
                             FStar_Util.Inl uu____7333  in
                           (uu____7318, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7299
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7399,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7401);
                                     FStar_Syntax_Syntax.sigrng = uu____7402;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7403;
                                     FStar_Syntax_Syntax.sigmeta = uu____7404;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7405;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7425 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7425
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7471 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7478 -> cache t  in
                       let uu____7479 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7479 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7554 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7554 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7640 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7700 = find_in_sigtab env lid  in
         match uu____7700 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7779) ->
          add_sigelts env ses
      | uu____7788 ->
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
            | uu____7802 -> ()))

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
        (fun uu___73_7829  ->
           match uu___73_7829 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7847 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____7900,lb::[]),uu____7902) ->
            let uu____7915 =
              let uu____7924 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____7933 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____7924, uu____7933)  in
            FStar_Pervasives_Native.Some uu____7915
        | FStar_Syntax_Syntax.Sig_let ((uu____7946,lbs),uu____7948) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____7984 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____7996 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____7996
                     then
                       let uu____8007 =
                         let uu____8016 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____8025 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____8016, uu____8025)  in
                       FStar_Pervasives_Native.Some uu____8007
                     else FStar_Pervasives_Native.None)
        | uu____8047 -> FStar_Pervasives_Native.None
  
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
          let uu____8100 =
            let uu____8109 =
              let uu____8114 =
                let uu____8115 =
                  let uu____8118 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____8118
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____8115)  in
              inst_tscheme1 uu____8114  in
            (uu____8109, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8100
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____8138,uu____8139) ->
          let uu____8144 =
            let uu____8153 =
              let uu____8158 =
                let uu____8159 =
                  let uu____8162 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____8162  in
                (us, uu____8159)  in
              inst_tscheme1 uu____8158  in
            (uu____8153, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8144
      | uu____8179 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____8257 =
          match uu____8257 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____8353,uvs,t,uu____8356,uu____8357,uu____8358);
                      FStar_Syntax_Syntax.sigrng = uu____8359;
                      FStar_Syntax_Syntax.sigquals = uu____8360;
                      FStar_Syntax_Syntax.sigmeta = uu____8361;
                      FStar_Syntax_Syntax.sigattrs = uu____8362;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8383 =
                     let uu____8392 = inst_tscheme1 (uvs, t)  in
                     (uu____8392, rng)  in
                   FStar_Pervasives_Native.Some uu____8383
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____8412;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____8414;
                      FStar_Syntax_Syntax.sigattrs = uu____8415;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8432 =
                     let uu____8433 = in_cur_mod env l  in uu____8433 = Yes
                      in
                   if uu____8432
                   then
                     let uu____8444 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____8444
                      then
                        let uu____8457 =
                          let uu____8466 = inst_tscheme1 (uvs, t)  in
                          (uu____8466, rng)  in
                        FStar_Pervasives_Native.Some uu____8457
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____8493 =
                        let uu____8502 = inst_tscheme1 (uvs, t)  in
                        (uu____8502, rng)  in
                      FStar_Pervasives_Native.Some uu____8493)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8523,uu____8524);
                      FStar_Syntax_Syntax.sigrng = uu____8525;
                      FStar_Syntax_Syntax.sigquals = uu____8526;
                      FStar_Syntax_Syntax.sigmeta = uu____8527;
                      FStar_Syntax_Syntax.sigattrs = uu____8528;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____8567 =
                          let uu____8576 = inst_tscheme1 (uvs, k)  in
                          (uu____8576, rng)  in
                        FStar_Pervasives_Native.Some uu____8567
                    | uu____8593 ->
                        let uu____8594 =
                          let uu____8603 =
                            let uu____8608 =
                              let uu____8609 =
                                let uu____8612 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8612
                                 in
                              (uvs, uu____8609)  in
                            inst_tscheme1 uu____8608  in
                          (uu____8603, rng)  in
                        FStar_Pervasives_Native.Some uu____8594)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8633,uu____8634);
                      FStar_Syntax_Syntax.sigrng = uu____8635;
                      FStar_Syntax_Syntax.sigquals = uu____8636;
                      FStar_Syntax_Syntax.sigmeta = uu____8637;
                      FStar_Syntax_Syntax.sigattrs = uu____8638;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____8678 =
                          let uu____8687 = inst_tscheme_with (uvs, k) us  in
                          (uu____8687, rng)  in
                        FStar_Pervasives_Native.Some uu____8678
                    | uu____8704 ->
                        let uu____8705 =
                          let uu____8714 =
                            let uu____8719 =
                              let uu____8720 =
                                let uu____8723 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8723
                                 in
                              (uvs, uu____8720)  in
                            inst_tscheme_with uu____8719 us  in
                          (uu____8714, rng)  in
                        FStar_Pervasives_Native.Some uu____8705)
               | FStar_Util.Inr se ->
                   let uu____8757 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____8778;
                          FStar_Syntax_Syntax.sigrng = uu____8779;
                          FStar_Syntax_Syntax.sigquals = uu____8780;
                          FStar_Syntax_Syntax.sigmeta = uu____8781;
                          FStar_Syntax_Syntax.sigattrs = uu____8782;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____8797 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____8757
                     (FStar_Util.map_option
                        (fun uu____8845  ->
                           match uu____8845 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____8876 =
          let uu____8887 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____8887 mapper  in
        match uu____8876 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            FStar_Pervasives_Native.Some
              ((us,
                 (let uu___94_8980 = t  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___94_8980.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                    FStar_Syntax_Syntax.vars =
                      (uu___94_8980.FStar_Syntax_Syntax.vars)
                  })), r)
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____9005 = lookup_qname env l  in
      match uu____9005 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9024 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9072 = try_lookup_bv env bv  in
      match uu____9072 with
      | FStar_Pervasives_Native.None  ->
          let uu____9087 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9087 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9102 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9103 =
            let uu____9104 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9104  in
          (uu____9102, uu____9103)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____9121 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____9121 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9187 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9187  in
          let uu____9188 =
            let uu____9197 =
              let uu____9202 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9202)  in
            (uu____9197, r1)  in
          FStar_Pervasives_Native.Some uu____9188
  
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
        let uu____9230 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____9230 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____9263,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____9288 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____9288  in
            let uu____9289 =
              let uu____9294 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____9294, r1)  in
            FStar_Pervasives_Native.Some uu____9289
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____9313 = try_lookup_lid env l  in
      match uu____9313 with
      | FStar_Pervasives_Native.None  ->
          let uu____9340 = name_not_found l  in
          FStar_Errors.raise_error uu____9340 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___74_9380  ->
              match uu___74_9380 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9382 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9397 = lookup_qname env lid  in
      match uu____9397 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9406,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9409;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9411;
              FStar_Syntax_Syntax.sigattrs = uu____9412;_},FStar_Pervasives_Native.None
            ),uu____9413)
          ->
          let uu____9462 =
            let uu____9473 =
              let uu____9478 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9478)  in
            (uu____9473, q)  in
          FStar_Pervasives_Native.Some uu____9462
      | uu____9495 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9512 = lookup_qname env lid  in
      match uu____9512 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9517,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9520;
              FStar_Syntax_Syntax.sigquals = uu____9521;
              FStar_Syntax_Syntax.sigmeta = uu____9522;
              FStar_Syntax_Syntax.sigattrs = uu____9523;_},FStar_Pervasives_Native.None
            ),uu____9524)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9573 ->
          let uu____9574 = name_not_found lid  in
          FStar_Errors.raise_error uu____9574 (FStar_Ident.range_of_lid lid)
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9593 = lookup_qname env lid  in
      match uu____9593 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9598,uvs,t,uu____9601,uu____9602,uu____9603);
              FStar_Syntax_Syntax.sigrng = uu____9604;
              FStar_Syntax_Syntax.sigquals = uu____9605;
              FStar_Syntax_Syntax.sigmeta = uu____9606;
              FStar_Syntax_Syntax.sigattrs = uu____9607;_},FStar_Pervasives_Native.None
            ),uu____9608)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9661 ->
          let uu____9662 = name_not_found lid  in
          FStar_Errors.raise_error uu____9662 (FStar_Ident.range_of_lid lid)
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9683 = lookup_qname env lid  in
      match uu____9683 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9690,uu____9691,uu____9692,uu____9693,uu____9694,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9696;
              FStar_Syntax_Syntax.sigquals = uu____9697;
              FStar_Syntax_Syntax.sigmeta = uu____9698;
              FStar_Syntax_Syntax.sigattrs = uu____9699;_},uu____9700),uu____9701)
          -> (true, dcs)
      | uu____9762 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____9771 = lookup_qname env lid  in
      match uu____9771 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9772,uu____9773,uu____9774,l,uu____9776,uu____9777);
              FStar_Syntax_Syntax.sigrng = uu____9778;
              FStar_Syntax_Syntax.sigquals = uu____9779;
              FStar_Syntax_Syntax.sigmeta = uu____9780;
              FStar_Syntax_Syntax.sigattrs = uu____9781;_},uu____9782),uu____9783)
          -> l
      | uu____9838 ->
          let uu____9839 =
            let uu____9840 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____9840  in
          failwith uu____9839
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9881) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9932,lbs),uu____9934) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____9962 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____9962
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9994 -> FStar_Pervasives_Native.None)
        | uu____9999 -> FStar_Pervasives_Native.None
  
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
        let uu____10023 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____10023
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____10046),uu____10047) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____10096 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10113 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____10113
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____10128 = lookup_qname env ftv  in
      match uu____10128 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10132) ->
          let uu____10177 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____10177 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10198,t),r) ->
               let uu____10213 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10213)
      | uu____10214 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____10221 = try_lookup_effect_lid env ftv  in
      match uu____10221 with
      | FStar_Pervasives_Native.None  ->
          let uu____10224 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10224 (FStar_Ident.range_of_lid ftv)
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
        let uu____10245 = lookup_qname env lid0  in
        match uu____10245 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10256);
                FStar_Syntax_Syntax.sigrng = uu____10257;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10259;
                FStar_Syntax_Syntax.sigattrs = uu____10260;_},FStar_Pervasives_Native.None
              ),uu____10261)
            ->
            let lid1 =
              let uu____10315 =
                let uu____10316 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10316
                 in
              FStar_Ident.set_lid_range lid uu____10315  in
            let uu____10317 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___75_10321  ->
                      match uu___75_10321 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10322 -> false))
               in
            if uu____10317
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10336 =
                      let uu____10337 =
                        let uu____10338 = get_range env  in
                        FStar_Range.string_of_range uu____10338  in
                      let uu____10339 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____10340 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10337 uu____10339 uu____10340
                       in
                    failwith uu____10336)
                  in
               match (binders, univs1) with
               | ([],uu____10347) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10364,uu____10365::uu____10366::uu____10367) ->
                   let uu____10372 =
                     let uu____10373 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____10374 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10373 uu____10374
                      in
                   failwith uu____10372
               | uu____10381 ->
                   let uu____10386 =
                     let uu____10391 =
                       let uu____10392 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____10392)  in
                     inst_tscheme_with uu____10391 insts  in
                   (match uu____10386 with
                    | (uu____10403,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____10406 =
                          let uu____10407 = FStar_Syntax_Subst.compress t1
                             in
                          uu____10407.FStar_Syntax_Syntax.n  in
                        (match uu____10406 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10454 -> failwith "Impossible")))
        | uu____10461 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10481 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____10481 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10494,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____10501 = find1 l2  in
            (match uu____10501 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____10508 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____10508 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10512 = find1 l  in
            (match uu____10512 with
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
      let uu____10526 = lookup_qname env l1  in
      match uu____10526 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10529;
              FStar_Syntax_Syntax.sigrng = uu____10530;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10532;
              FStar_Syntax_Syntax.sigattrs = uu____10533;_},uu____10534),uu____10535)
          -> q
      | uu____10586 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10599 =
          let uu____10600 =
            let uu____10601 = FStar_Util.string_of_int i  in
            let uu____10602 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10601 uu____10602
             in
          failwith uu____10600  in
        let uu____10603 = lookup_datacon env lid  in
        match uu____10603 with
        | (uu____10608,t) ->
            let uu____10610 =
              let uu____10611 = FStar_Syntax_Subst.compress t  in
              uu____10611.FStar_Syntax_Syntax.n  in
            (match uu____10610 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10615) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____10646 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____10646
                      FStar_Pervasives_Native.fst)
             | uu____10655 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____10662 = lookup_qname env l  in
      match uu____10662 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10663,uu____10664,uu____10665);
              FStar_Syntax_Syntax.sigrng = uu____10666;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10668;
              FStar_Syntax_Syntax.sigattrs = uu____10669;_},uu____10670),uu____10671)
          ->
          FStar_Util.for_some
            (fun uu___76_10724  ->
               match uu___76_10724 with
               | FStar_Syntax_Syntax.Projector uu____10725 -> true
               | uu____10730 -> false) quals
      | uu____10731 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____10738 = lookup_qname env lid  in
      match uu____10738 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10739,uu____10740,uu____10741,uu____10742,uu____10743,uu____10744);
              FStar_Syntax_Syntax.sigrng = uu____10745;
              FStar_Syntax_Syntax.sigquals = uu____10746;
              FStar_Syntax_Syntax.sigmeta = uu____10747;
              FStar_Syntax_Syntax.sigattrs = uu____10748;_},uu____10749),uu____10750)
          -> true
      | uu____10805 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____10812 = lookup_qname env lid  in
      match uu____10812 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10813,uu____10814,uu____10815,uu____10816,uu____10817,uu____10818);
              FStar_Syntax_Syntax.sigrng = uu____10819;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10821;
              FStar_Syntax_Syntax.sigattrs = uu____10822;_},uu____10823),uu____10824)
          ->
          FStar_Util.for_some
            (fun uu___77_10885  ->
               match uu___77_10885 with
               | FStar_Syntax_Syntax.RecordType uu____10886 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10895 -> true
               | uu____10904 -> false) quals
      | uu____10905 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____10909,uu____10910);
            FStar_Syntax_Syntax.sigrng = uu____10911;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____10913;
            FStar_Syntax_Syntax.sigattrs = uu____10914;_},uu____10915),uu____10916)
        ->
        FStar_Util.for_some
          (fun uu___78_10973  ->
             match uu___78_10973 with
             | FStar_Syntax_Syntax.Action uu____10974 -> true
             | uu____10975 -> false) quals
    | uu____10976 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____10983 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____10983
  
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
      let uu____10993 =
        let uu____10994 = FStar_Syntax_Util.un_uinst head1  in
        uu____10994.FStar_Syntax_Syntax.n  in
      match uu____10993 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10998 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11005 = lookup_qname env l  in
      match uu____11005 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11007),uu____11008) ->
          FStar_Util.for_some
            (fun uu___79_11056  ->
               match uu___79_11056 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11057 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11058 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11123 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11139) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11156 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11163 ->
                 FStar_Pervasives_Native.Some true
             | uu____11180 -> FStar_Pervasives_Native.Some false)
         in
      let uu____11181 =
        let uu____11184 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____11184 mapper  in
      match uu____11181 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____11230 = lookup_qname env lid  in
      match uu____11230 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11231,uu____11232,tps,uu____11234,uu____11235,uu____11236);
              FStar_Syntax_Syntax.sigrng = uu____11237;
              FStar_Syntax_Syntax.sigquals = uu____11238;
              FStar_Syntax_Syntax.sigmeta = uu____11239;
              FStar_Syntax_Syntax.sigattrs = uu____11240;_},uu____11241),uu____11242)
          -> FStar_List.length tps
      | uu____11305 ->
          let uu____11306 = name_not_found lid  in
          FStar_Errors.raise_error uu____11306 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____11350  ->
              match uu____11350 with
              | (d,uu____11358) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____11369 = effect_decl_opt env l  in
      match uu____11369 with
      | FStar_Pervasives_Native.None  ->
          let uu____11384 = name_not_found l  in
          FStar_Errors.raise_error uu____11384 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____11410  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11425  ->
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
            (let uu____11458 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11511  ->
                       match uu____11511 with
                       | (m1,m2,uu____11524,uu____11525,uu____11526) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____11458 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11543 =
                   let uu____11548 =
                     let uu____11549 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____11550 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11549
                       uu____11550
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____11548)
                    in
                 FStar_Errors.raise_error uu____11543 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11557,uu____11558,m3,j1,j2) -> (m3, j1, j2))
  
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
  'Auu____11595 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11595)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11622 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11648  ->
                match uu____11648 with
                | (d,uu____11654) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____11622 with
      | FStar_Pervasives_Native.None  ->
          let uu____11665 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____11665
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11678 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____11678 with
           | (uu____11689,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11699)::(wp,uu____11701)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11737 -> failwith "Impossible"))
  
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
                 let uu____11780 = get_range env  in
                 let uu____11781 =
                   let uu____11784 =
                     let uu____11785 =
                       let uu____11800 =
                         let uu____11803 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____11803]  in
                       (null_wp, uu____11800)  in
                     FStar_Syntax_Syntax.Tm_app uu____11785  in
                   FStar_Syntax_Syntax.mk uu____11784  in
                 uu____11781 FStar_Pervasives_Native.None uu____11780  in
               let uu____11809 =
                 let uu____11810 =
                   let uu____11819 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____11819]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11810;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____11809)
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___95_11828 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___95_11828.order);
              joins = (uu___95_11828.joins)
            }  in
          let uu___96_11837 = env  in
          {
            solver = (uu___96_11837.solver);
            range = (uu___96_11837.range);
            curmodule = (uu___96_11837.curmodule);
            gamma = (uu___96_11837.gamma);
            gamma_cache = (uu___96_11837.gamma_cache);
            modules = (uu___96_11837.modules);
            expected_typ = (uu___96_11837.expected_typ);
            sigtab = (uu___96_11837.sigtab);
            is_pattern = (uu___96_11837.is_pattern);
            instantiate_imp = (uu___96_11837.instantiate_imp);
            effects;
            generalize = (uu___96_11837.generalize);
            letrecs = (uu___96_11837.letrecs);
            top_level = (uu___96_11837.top_level);
            check_uvars = (uu___96_11837.check_uvars);
            use_eq = (uu___96_11837.use_eq);
            is_iface = (uu___96_11837.is_iface);
            admit = (uu___96_11837.admit);
            lax = (uu___96_11837.lax);
            lax_universes = (uu___96_11837.lax_universes);
            failhard = (uu___96_11837.failhard);
            nosynth = (uu___96_11837.nosynth);
            tc_term = (uu___96_11837.tc_term);
            type_of = (uu___96_11837.type_of);
            universe_of = (uu___96_11837.universe_of);
            check_type_of = (uu___96_11837.check_type_of);
            use_bv_sorts = (uu___96_11837.use_bv_sorts);
            qname_and_index = (uu___96_11837.qname_and_index);
            proof_ns = (uu___96_11837.proof_ns);
            synth = (uu___96_11837.synth);
            is_native_tactic = (uu___96_11837.is_native_tactic);
            identifier_info = (uu___96_11837.identifier_info);
            tc_hooks = (uu___96_11837.tc_hooks);
            dsenv = (uu___96_11837.dsenv);
            dep_graph = (uu___96_11837.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____11857 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____11857  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____11971 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____11972 = l1 u t wp e  in
                                l2 u t uu____11971 uu____11972))
                | uu____11973 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12021 = inst_tscheme_with lift_t [u]  in
            match uu____12021 with
            | (uu____12028,lift_t1) ->
                let uu____12030 =
                  let uu____12033 =
                    let uu____12034 =
                      let uu____12049 =
                        let uu____12052 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12053 =
                          let uu____12056 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12056]  in
                        uu____12052 :: uu____12053  in
                      (lift_t1, uu____12049)  in
                    FStar_Syntax_Syntax.Tm_app uu____12034  in
                  FStar_Syntax_Syntax.mk uu____12033  in
                uu____12030 FStar_Pervasives_Native.None
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
            let uu____12106 = inst_tscheme_with lift_t [u]  in
            match uu____12106 with
            | (uu____12113,lift_t1) ->
                let uu____12115 =
                  let uu____12118 =
                    let uu____12119 =
                      let uu____12134 =
                        let uu____12137 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12138 =
                          let uu____12141 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12142 =
                            let uu____12145 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12145]  in
                          uu____12141 :: uu____12142  in
                        uu____12137 :: uu____12138  in
                      (lift_t1, uu____12134)  in
                    FStar_Syntax_Syntax.Tm_app uu____12119  in
                  FStar_Syntax_Syntax.mk uu____12118  in
                uu____12115 FStar_Pervasives_Native.None
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
              let uu____12187 =
                let uu____12188 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____12188
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____12187  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____12192 =
              let uu____12193 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____12193  in
            let uu____12194 =
              let uu____12195 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12217 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____12217)
                 in
              FStar_Util.dflt "none" uu____12195  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12192
              uu____12194
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12243  ->
                    match uu____12243 with
                    | (e,uu____12251) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____12270 =
            match uu____12270 with
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
              let uu____12308 =
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
                                    (let uu____12329 =
                                       let uu____12338 =
                                         find_edge order1 (i, k)  in
                                       let uu____12341 =
                                         find_edge order1 (k, j)  in
                                       (uu____12338, uu____12341)  in
                                     match uu____12329 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12356 =
                                           compose_edges e1 e2  in
                                         [uu____12356]
                                     | uu____12357 -> [])))))
                 in
              FStar_List.append order1 uu____12308  in
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
                   let uu____12387 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12389 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____12389
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____12387
                   then
                     let uu____12394 =
                       let uu____12399 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12399)
                        in
                     let uu____12400 = get_range env  in
                     FStar_Errors.raise_error uu____12394 uu____12400
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
                                            let uu____12525 =
                                              let uu____12534 =
                                                find_edge order2 (i, k)  in
                                              let uu____12537 =
                                                find_edge order2 (j, k)  in
                                              (uu____12534, uu____12537)  in
                                            match uu____12525 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12579,uu____12580)
                                                     ->
                                                     let uu____12587 =
                                                       let uu____12592 =
                                                         let uu____12593 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12593
                                                          in
                                                       let uu____12596 =
                                                         let uu____12597 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12597
                                                          in
                                                       (uu____12592,
                                                         uu____12596)
                                                        in
                                                     (match uu____12587 with
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
                                            | uu____12632 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___97_12705 = env.effects  in
              { decls = (uu___97_12705.decls); order = order2; joins }  in
            let uu___98_12706 = env  in
            {
              solver = (uu___98_12706.solver);
              range = (uu___98_12706.range);
              curmodule = (uu___98_12706.curmodule);
              gamma = (uu___98_12706.gamma);
              gamma_cache = (uu___98_12706.gamma_cache);
              modules = (uu___98_12706.modules);
              expected_typ = (uu___98_12706.expected_typ);
              sigtab = (uu___98_12706.sigtab);
              is_pattern = (uu___98_12706.is_pattern);
              instantiate_imp = (uu___98_12706.instantiate_imp);
              effects;
              generalize = (uu___98_12706.generalize);
              letrecs = (uu___98_12706.letrecs);
              top_level = (uu___98_12706.top_level);
              check_uvars = (uu___98_12706.check_uvars);
              use_eq = (uu___98_12706.use_eq);
              is_iface = (uu___98_12706.is_iface);
              admit = (uu___98_12706.admit);
              lax = (uu___98_12706.lax);
              lax_universes = (uu___98_12706.lax_universes);
              failhard = (uu___98_12706.failhard);
              nosynth = (uu___98_12706.nosynth);
              tc_term = (uu___98_12706.tc_term);
              type_of = (uu___98_12706.type_of);
              universe_of = (uu___98_12706.universe_of);
              check_type_of = (uu___98_12706.check_type_of);
              use_bv_sorts = (uu___98_12706.use_bv_sorts);
              qname_and_index = (uu___98_12706.qname_and_index);
              proof_ns = (uu___98_12706.proof_ns);
              synth = (uu___98_12706.synth);
              is_native_tactic = (uu___98_12706.is_native_tactic);
              identifier_info = (uu___98_12706.identifier_info);
              tc_hooks = (uu___98_12706.tc_hooks);
              dsenv = (uu___98_12706.dsenv);
              dep_graph = (uu___98_12706.dep_graph)
            }))
      | uu____12707 -> env
  
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
        | uu____12731 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____12739 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____12739 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12756 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____12756 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12774 =
                     let uu____12779 =
                       let uu____12780 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____12785 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____12792 =
                         let uu____12793 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____12793  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____12780 uu____12785 uu____12792
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____12779)
                      in
                   FStar_Errors.raise_error uu____12774
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____12798 =
                     let uu____12807 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____12807 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____12824  ->
                        fun uu____12825  ->
                          match (uu____12824, uu____12825) with
                          | ((x,uu____12847),(t,uu____12849)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12798
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____12868 =
                     let uu___99_12869 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___99_12869.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___99_12869.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___99_12869.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___99_12869.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____12868
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
          let uu____12891 = effect_decl_opt env effect_name  in
          match uu____12891 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12924 =
                only_reifiable &&
                  (let uu____12926 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____12926)
                 in
              if uu____12924
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12942 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____12961 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____12990 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____12990
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____12991 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____12991
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13001 =
                       let uu____13004 = get_range env  in
                       let uu____13005 =
                         let uu____13008 =
                           let uu____13009 =
                             let uu____13024 =
                               let uu____13027 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13027; wp]  in
                             (repr, uu____13024)  in
                           FStar_Syntax_Syntax.Tm_app uu____13009  in
                         FStar_Syntax_Syntax.mk uu____13008  in
                       uu____13005 FStar_Pervasives_Native.None uu____13004
                        in
                     FStar_Pervasives_Native.Some uu____13001)
  
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
          let uu____13073 =
            let uu____13078 =
              let uu____13079 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13079
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13078)  in
          let uu____13080 = get_range env  in
          FStar_Errors.raise_error uu____13073 uu____13080  in
        let uu____13081 = effect_repr_aux true env c u_c  in
        match uu____13081 with
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
      | uu____13115 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____13122 =
        let uu____13123 = FStar_Syntax_Subst.compress t  in
        uu____13123.FStar_Syntax_Syntax.n  in
      match uu____13122 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13126,c) ->
          is_reifiable_comp env c
      | uu____13144 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13166)::uu____13167 -> x :: rest
        | (Binding_sig_inst uu____13176)::uu____13177 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13192 = push1 x rest1  in local :: uu____13192
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___100_13196 = env  in
       let uu____13197 = push1 s env.gamma  in
       {
         solver = (uu___100_13196.solver);
         range = (uu___100_13196.range);
         curmodule = (uu___100_13196.curmodule);
         gamma = uu____13197;
         gamma_cache = (uu___100_13196.gamma_cache);
         modules = (uu___100_13196.modules);
         expected_typ = (uu___100_13196.expected_typ);
         sigtab = (uu___100_13196.sigtab);
         is_pattern = (uu___100_13196.is_pattern);
         instantiate_imp = (uu___100_13196.instantiate_imp);
         effects = (uu___100_13196.effects);
         generalize = (uu___100_13196.generalize);
         letrecs = (uu___100_13196.letrecs);
         top_level = (uu___100_13196.top_level);
         check_uvars = (uu___100_13196.check_uvars);
         use_eq = (uu___100_13196.use_eq);
         is_iface = (uu___100_13196.is_iface);
         admit = (uu___100_13196.admit);
         lax = (uu___100_13196.lax);
         lax_universes = (uu___100_13196.lax_universes);
         failhard = (uu___100_13196.failhard);
         nosynth = (uu___100_13196.nosynth);
         tc_term = (uu___100_13196.tc_term);
         type_of = (uu___100_13196.type_of);
         universe_of = (uu___100_13196.universe_of);
         check_type_of = (uu___100_13196.check_type_of);
         use_bv_sorts = (uu___100_13196.use_bv_sorts);
         qname_and_index = (uu___100_13196.qname_and_index);
         proof_ns = (uu___100_13196.proof_ns);
         synth = (uu___100_13196.synth);
         is_native_tactic = (uu___100_13196.is_native_tactic);
         identifier_info = (uu___100_13196.identifier_info);
         tc_hooks = (uu___100_13196.tc_hooks);
         dsenv = (uu___100_13196.dsenv);
         dep_graph = (uu___100_13196.dep_graph)
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
      let uu___101_13227 = env  in
      {
        solver = (uu___101_13227.solver);
        range = (uu___101_13227.range);
        curmodule = (uu___101_13227.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___101_13227.gamma_cache);
        modules = (uu___101_13227.modules);
        expected_typ = (uu___101_13227.expected_typ);
        sigtab = (uu___101_13227.sigtab);
        is_pattern = (uu___101_13227.is_pattern);
        instantiate_imp = (uu___101_13227.instantiate_imp);
        effects = (uu___101_13227.effects);
        generalize = (uu___101_13227.generalize);
        letrecs = (uu___101_13227.letrecs);
        top_level = (uu___101_13227.top_level);
        check_uvars = (uu___101_13227.check_uvars);
        use_eq = (uu___101_13227.use_eq);
        is_iface = (uu___101_13227.is_iface);
        admit = (uu___101_13227.admit);
        lax = (uu___101_13227.lax);
        lax_universes = (uu___101_13227.lax_universes);
        failhard = (uu___101_13227.failhard);
        nosynth = (uu___101_13227.nosynth);
        tc_term = (uu___101_13227.tc_term);
        type_of = (uu___101_13227.type_of);
        universe_of = (uu___101_13227.universe_of);
        check_type_of = (uu___101_13227.check_type_of);
        use_bv_sorts = (uu___101_13227.use_bv_sorts);
        qname_and_index = (uu___101_13227.qname_and_index);
        proof_ns = (uu___101_13227.proof_ns);
        synth = (uu___101_13227.synth);
        is_native_tactic = (uu___101_13227.is_native_tactic);
        identifier_info = (uu___101_13227.identifier_info);
        tc_hooks = (uu___101_13227.tc_hooks);
        dsenv = (uu___101_13227.dsenv);
        dep_graph = (uu___101_13227.dep_graph)
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
            (let uu___102_13258 = env  in
             {
               solver = (uu___102_13258.solver);
               range = (uu___102_13258.range);
               curmodule = (uu___102_13258.curmodule);
               gamma = rest;
               gamma_cache = (uu___102_13258.gamma_cache);
               modules = (uu___102_13258.modules);
               expected_typ = (uu___102_13258.expected_typ);
               sigtab = (uu___102_13258.sigtab);
               is_pattern = (uu___102_13258.is_pattern);
               instantiate_imp = (uu___102_13258.instantiate_imp);
               effects = (uu___102_13258.effects);
               generalize = (uu___102_13258.generalize);
               letrecs = (uu___102_13258.letrecs);
               top_level = (uu___102_13258.top_level);
               check_uvars = (uu___102_13258.check_uvars);
               use_eq = (uu___102_13258.use_eq);
               is_iface = (uu___102_13258.is_iface);
               admit = (uu___102_13258.admit);
               lax = (uu___102_13258.lax);
               lax_universes = (uu___102_13258.lax_universes);
               failhard = (uu___102_13258.failhard);
               nosynth = (uu___102_13258.nosynth);
               tc_term = (uu___102_13258.tc_term);
               type_of = (uu___102_13258.type_of);
               universe_of = (uu___102_13258.universe_of);
               check_type_of = (uu___102_13258.check_type_of);
               use_bv_sorts = (uu___102_13258.use_bv_sorts);
               qname_and_index = (uu___102_13258.qname_and_index);
               proof_ns = (uu___102_13258.proof_ns);
               synth = (uu___102_13258.synth);
               is_native_tactic = (uu___102_13258.is_native_tactic);
               identifier_info = (uu___102_13258.identifier_info);
               tc_hooks = (uu___102_13258.tc_hooks);
               dsenv = (uu___102_13258.dsenv);
               dep_graph = (uu___102_13258.dep_graph)
             }))
    | uu____13259 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13281  ->
             match uu____13281 with | (x,uu____13287) -> push_bv env1 x) env
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
            let uu___103_13315 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___103_13315.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___103_13315.FStar_Syntax_Syntax.index);
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
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___104_13345 = env  in
       {
         solver = (uu___104_13345.solver);
         range = (uu___104_13345.range);
         curmodule = (uu___104_13345.curmodule);
         gamma = [];
         gamma_cache = (uu___104_13345.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___104_13345.sigtab);
         is_pattern = (uu___104_13345.is_pattern);
         instantiate_imp = (uu___104_13345.instantiate_imp);
         effects = (uu___104_13345.effects);
         generalize = (uu___104_13345.generalize);
         letrecs = (uu___104_13345.letrecs);
         top_level = (uu___104_13345.top_level);
         check_uvars = (uu___104_13345.check_uvars);
         use_eq = (uu___104_13345.use_eq);
         is_iface = (uu___104_13345.is_iface);
         admit = (uu___104_13345.admit);
         lax = (uu___104_13345.lax);
         lax_universes = (uu___104_13345.lax_universes);
         failhard = (uu___104_13345.failhard);
         nosynth = (uu___104_13345.nosynth);
         tc_term = (uu___104_13345.tc_term);
         type_of = (uu___104_13345.type_of);
         universe_of = (uu___104_13345.universe_of);
         check_type_of = (uu___104_13345.check_type_of);
         use_bv_sorts = (uu___104_13345.use_bv_sorts);
         qname_and_index = (uu___104_13345.qname_and_index);
         proof_ns = (uu___104_13345.proof_ns);
         synth = (uu___104_13345.synth);
         is_native_tactic = (uu___104_13345.is_native_tactic);
         identifier_info = (uu___104_13345.identifier_info);
         tc_hooks = (uu___104_13345.tc_hooks);
         dsenv = (uu___104_13345.dsenv);
         dep_graph = (uu___104_13345.dep_graph)
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
        let uu____13377 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____13377 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____13405 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____13405)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___105_13418 = env  in
      {
        solver = (uu___105_13418.solver);
        range = (uu___105_13418.range);
        curmodule = (uu___105_13418.curmodule);
        gamma = (uu___105_13418.gamma);
        gamma_cache = (uu___105_13418.gamma_cache);
        modules = (uu___105_13418.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___105_13418.sigtab);
        is_pattern = (uu___105_13418.is_pattern);
        instantiate_imp = (uu___105_13418.instantiate_imp);
        effects = (uu___105_13418.effects);
        generalize = (uu___105_13418.generalize);
        letrecs = (uu___105_13418.letrecs);
        top_level = (uu___105_13418.top_level);
        check_uvars = (uu___105_13418.check_uvars);
        use_eq = false;
        is_iface = (uu___105_13418.is_iface);
        admit = (uu___105_13418.admit);
        lax = (uu___105_13418.lax);
        lax_universes = (uu___105_13418.lax_universes);
        failhard = (uu___105_13418.failhard);
        nosynth = (uu___105_13418.nosynth);
        tc_term = (uu___105_13418.tc_term);
        type_of = (uu___105_13418.type_of);
        universe_of = (uu___105_13418.universe_of);
        check_type_of = (uu___105_13418.check_type_of);
        use_bv_sorts = (uu___105_13418.use_bv_sorts);
        qname_and_index = (uu___105_13418.qname_and_index);
        proof_ns = (uu___105_13418.proof_ns);
        synth = (uu___105_13418.synth);
        is_native_tactic = (uu___105_13418.is_native_tactic);
        identifier_info = (uu___105_13418.identifier_info);
        tc_hooks = (uu___105_13418.tc_hooks);
        dsenv = (uu___105_13418.dsenv);
        dep_graph = (uu___105_13418.dep_graph)
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
    let uu____13442 = expected_typ env_  in
    ((let uu___106_13448 = env_  in
      {
        solver = (uu___106_13448.solver);
        range = (uu___106_13448.range);
        curmodule = (uu___106_13448.curmodule);
        gamma = (uu___106_13448.gamma);
        gamma_cache = (uu___106_13448.gamma_cache);
        modules = (uu___106_13448.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___106_13448.sigtab);
        is_pattern = (uu___106_13448.is_pattern);
        instantiate_imp = (uu___106_13448.instantiate_imp);
        effects = (uu___106_13448.effects);
        generalize = (uu___106_13448.generalize);
        letrecs = (uu___106_13448.letrecs);
        top_level = (uu___106_13448.top_level);
        check_uvars = (uu___106_13448.check_uvars);
        use_eq = false;
        is_iface = (uu___106_13448.is_iface);
        admit = (uu___106_13448.admit);
        lax = (uu___106_13448.lax);
        lax_universes = (uu___106_13448.lax_universes);
        failhard = (uu___106_13448.failhard);
        nosynth = (uu___106_13448.nosynth);
        tc_term = (uu___106_13448.tc_term);
        type_of = (uu___106_13448.type_of);
        universe_of = (uu___106_13448.universe_of);
        check_type_of = (uu___106_13448.check_type_of);
        use_bv_sorts = (uu___106_13448.use_bv_sorts);
        qname_and_index = (uu___106_13448.qname_and_index);
        proof_ns = (uu___106_13448.proof_ns);
        synth = (uu___106_13448.synth);
        is_native_tactic = (uu___106_13448.is_native_tactic);
        identifier_info = (uu___106_13448.identifier_info);
        tc_hooks = (uu___106_13448.tc_hooks);
        dsenv = (uu___106_13448.dsenv);
        dep_graph = (uu___106_13448.dep_graph)
      }), uu____13442)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13461 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___80_13471  ->
                    match uu___80_13471 with
                    | Binding_sig (uu____13474,se) -> [se]
                    | uu____13480 -> []))
             in
          FStar_All.pipe_right uu____13461 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___107_13487 = env  in
       {
         solver = (uu___107_13487.solver);
         range = (uu___107_13487.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___107_13487.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___107_13487.expected_typ);
         sigtab = (uu___107_13487.sigtab);
         is_pattern = (uu___107_13487.is_pattern);
         instantiate_imp = (uu___107_13487.instantiate_imp);
         effects = (uu___107_13487.effects);
         generalize = (uu___107_13487.generalize);
         letrecs = (uu___107_13487.letrecs);
         top_level = (uu___107_13487.top_level);
         check_uvars = (uu___107_13487.check_uvars);
         use_eq = (uu___107_13487.use_eq);
         is_iface = (uu___107_13487.is_iface);
         admit = (uu___107_13487.admit);
         lax = (uu___107_13487.lax);
         lax_universes = (uu___107_13487.lax_universes);
         failhard = (uu___107_13487.failhard);
         nosynth = (uu___107_13487.nosynth);
         tc_term = (uu___107_13487.tc_term);
         type_of = (uu___107_13487.type_of);
         universe_of = (uu___107_13487.universe_of);
         check_type_of = (uu___107_13487.check_type_of);
         use_bv_sorts = (uu___107_13487.use_bv_sorts);
         qname_and_index = (uu___107_13487.qname_and_index);
         proof_ns = (uu___107_13487.proof_ns);
         synth = (uu___107_13487.synth);
         is_native_tactic = (uu___107_13487.is_native_tactic);
         identifier_info = (uu___107_13487.identifier_info);
         tc_hooks = (uu___107_13487.tc_hooks);
         dsenv = (uu___107_13487.dsenv);
         dep_graph = (uu___107_13487.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13568)::tl1 -> aux out tl1
      | (Binding_lid (uu____13572,(uu____13573,t)))::tl1 ->
          let uu____13588 =
            let uu____13595 = FStar_Syntax_Free.uvars t  in
            ext out uu____13595  in
          aux uu____13588 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13602;
            FStar_Syntax_Syntax.index = uu____13603;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13610 =
            let uu____13617 = FStar_Syntax_Free.uvars t  in
            ext out uu____13617  in
          aux uu____13610 tl1
      | (Binding_sig uu____13624)::uu____13625 -> out
      | (Binding_sig_inst uu____13634)::uu____13635 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13690)::tl1 -> aux out tl1
      | (Binding_univ uu____13702)::tl1 -> aux out tl1
      | (Binding_lid (uu____13706,(uu____13707,t)))::tl1 ->
          let uu____13722 =
            let uu____13725 = FStar_Syntax_Free.univs t  in
            ext out uu____13725  in
          aux uu____13722 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13728;
            FStar_Syntax_Syntax.index = uu____13729;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13736 =
            let uu____13739 = FStar_Syntax_Free.univs t  in
            ext out uu____13739  in
          aux uu____13736 tl1
      | (Binding_sig uu____13742)::uu____13743 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13796)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13812 = FStar_Util.fifo_set_add uname out  in
          aux uu____13812 tl1
      | (Binding_lid (uu____13815,(uu____13816,t)))::tl1 ->
          let uu____13831 =
            let uu____13834 = FStar_Syntax_Free.univnames t  in
            ext out uu____13834  in
          aux uu____13831 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13837;
            FStar_Syntax_Syntax.index = uu____13838;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13845 =
            let uu____13848 = FStar_Syntax_Free.univnames t  in
            ext out uu____13848  in
          aux uu____13845 tl1
      | (Binding_sig uu____13851)::uu____13852 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___81_13876  ->
            match uu___81_13876 with
            | Binding_var x -> [x]
            | Binding_lid uu____13880 -> []
            | Binding_sig uu____13885 -> []
            | Binding_univ uu____13892 -> []
            | Binding_sig_inst uu____13893 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____13909 =
      let uu____13912 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____13912
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____13909 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____13934 =
      let uu____13935 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___82_13945  ->
                match uu___82_13945 with
                | Binding_var x ->
                    let uu____13947 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____13947
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13950) ->
                    let uu____13951 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____13951
                | Binding_sig (ls,uu____13953) ->
                    let uu____13958 =
                      let uu____13959 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____13959
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____13958
                | Binding_sig_inst (ls,uu____13969,uu____13970) ->
                    let uu____13975 =
                      let uu____13976 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____13976
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____13975))
         in
      FStar_All.pipe_right uu____13935 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____13934 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____13993 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____13993
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14021  ->
                 fun uu____14022  ->
                   match (uu____14021, uu____14022) with
                   | ((b1,uu____14040),(b2,uu____14042)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___83_14084  ->
    match uu___83_14084 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14085 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___84_14103  ->
             match uu___84_14103 with
             | Binding_sig (lids,uu____14109) -> FStar_List.append lids keys
             | uu____14114 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14120  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14154) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14173,uu____14174) -> false  in
      let uu____14183 =
        FStar_List.tryFind
          (fun uu____14201  ->
             match uu____14201 with | (p,uu____14209) -> list_prefix p path)
          env.proof_ns
         in
      match uu____14183 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14220,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14238 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____14238
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___108_14250 = e  in
        {
          solver = (uu___108_14250.solver);
          range = (uu___108_14250.range);
          curmodule = (uu___108_14250.curmodule);
          gamma = (uu___108_14250.gamma);
          gamma_cache = (uu___108_14250.gamma_cache);
          modules = (uu___108_14250.modules);
          expected_typ = (uu___108_14250.expected_typ);
          sigtab = (uu___108_14250.sigtab);
          is_pattern = (uu___108_14250.is_pattern);
          instantiate_imp = (uu___108_14250.instantiate_imp);
          effects = (uu___108_14250.effects);
          generalize = (uu___108_14250.generalize);
          letrecs = (uu___108_14250.letrecs);
          top_level = (uu___108_14250.top_level);
          check_uvars = (uu___108_14250.check_uvars);
          use_eq = (uu___108_14250.use_eq);
          is_iface = (uu___108_14250.is_iface);
          admit = (uu___108_14250.admit);
          lax = (uu___108_14250.lax);
          lax_universes = (uu___108_14250.lax_universes);
          failhard = (uu___108_14250.failhard);
          nosynth = (uu___108_14250.nosynth);
          tc_term = (uu___108_14250.tc_term);
          type_of = (uu___108_14250.type_of);
          universe_of = (uu___108_14250.universe_of);
          check_type_of = (uu___108_14250.check_type_of);
          use_bv_sorts = (uu___108_14250.use_bv_sorts);
          qname_and_index = (uu___108_14250.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___108_14250.synth);
          is_native_tactic = (uu___108_14250.is_native_tactic);
          identifier_info = (uu___108_14250.identifier_info);
          tc_hooks = (uu___108_14250.tc_hooks);
          dsenv = (uu___108_14250.dsenv);
          dep_graph = (uu___108_14250.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___109_14276 = e  in
      {
        solver = (uu___109_14276.solver);
        range = (uu___109_14276.range);
        curmodule = (uu___109_14276.curmodule);
        gamma = (uu___109_14276.gamma);
        gamma_cache = (uu___109_14276.gamma_cache);
        modules = (uu___109_14276.modules);
        expected_typ = (uu___109_14276.expected_typ);
        sigtab = (uu___109_14276.sigtab);
        is_pattern = (uu___109_14276.is_pattern);
        instantiate_imp = (uu___109_14276.instantiate_imp);
        effects = (uu___109_14276.effects);
        generalize = (uu___109_14276.generalize);
        letrecs = (uu___109_14276.letrecs);
        top_level = (uu___109_14276.top_level);
        check_uvars = (uu___109_14276.check_uvars);
        use_eq = (uu___109_14276.use_eq);
        is_iface = (uu___109_14276.is_iface);
        admit = (uu___109_14276.admit);
        lax = (uu___109_14276.lax);
        lax_universes = (uu___109_14276.lax_universes);
        failhard = (uu___109_14276.failhard);
        nosynth = (uu___109_14276.nosynth);
        tc_term = (uu___109_14276.tc_term);
        type_of = (uu___109_14276.type_of);
        universe_of = (uu___109_14276.universe_of);
        check_type_of = (uu___109_14276.check_type_of);
        use_bv_sorts = (uu___109_14276.use_bv_sorts);
        qname_and_index = (uu___109_14276.qname_and_index);
        proof_ns = ns;
        synth = (uu___109_14276.synth);
        is_native_tactic = (uu___109_14276.is_native_tactic);
        identifier_info = (uu___109_14276.identifier_info);
        tc_hooks = (uu___109_14276.tc_hooks);
        dsenv = (uu___109_14276.dsenv);
        dep_graph = (uu___109_14276.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____14287 = FStar_Syntax_Free.names t  in
      let uu____14290 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14287 uu____14290
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____14307 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____14307
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14313 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____14313
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____14328 =
      match uu____14328 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14344 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____14344)
       in
    let uu____14346 =
      let uu____14349 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____14349 FStar_List.rev  in
    FStar_All.pipe_right uu____14346 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____14366  -> ());
    push = (fun uu____14368  -> ());
    pop = (fun uu____14370  -> ());
    encode_modul = (fun uu____14373  -> fun uu____14374  -> ());
    encode_sig = (fun uu____14377  -> fun uu____14378  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14384 =
             let uu____14391 = FStar_Options.peek ()  in (e, g, uu____14391)
              in
           [uu____14384]);
    solve = (fun uu____14407  -> fun uu____14408  -> fun uu____14409  -> ());
    finish = (fun uu____14415  -> ());
    refresh = (fun uu____14417  -> ())
  } 