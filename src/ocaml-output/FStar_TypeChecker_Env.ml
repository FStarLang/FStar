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
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____43 -> false
  
let __proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_lid : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____59 -> false
  
let __proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let uu___is_Binding_sig : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____89 -> false
  
let __proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let uu___is_Binding_univ : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____119 -> false
  
let __proj__Binding_univ__item___0 : binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let uu___is_Binding_sig_inst : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____139 -> false
  
let __proj__Binding_sig_inst__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0 
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac [@@deriving show]
let uu___is_NoDelta : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____178 -> false
  
let uu___is_Inlining : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____182 -> false
  
let uu___is_Eager_unfolding_only : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____186 -> false
  
let uu___is_Unfold : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____191 -> false
  
let __proj__Unfold__item___0 : delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0 
let uu___is_UnfoldTac : delta_level -> Prims.bool =
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
let __proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
  
let __proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
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
let __proj__Mkedge__item__msource : edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
  
let __proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
  
let __proj__Mkedge__item__mlift : edge -> mlift =
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
let __proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
  
let __proj__Mkeffects__item__order : effects -> edge Prims.list =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
  
let __proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
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
let __proj__Mkenv__item__solver : env -> solver_t =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__solver
  
let __proj__Mkenv__item__range : env -> FStar_Range.range =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__range
  
let __proj__Mkenv__item__curmodule : env -> FStar_Ident.lident =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
  
let __proj__Mkenv__item__gamma : env -> binding Prims.list =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma
  
let __proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma_cache
  
let __proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__modules
  
let __proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__expected_typ
  
let __proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__sigtab
  
let __proj__Mkenv__item__is_pattern : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_pattern
  
let __proj__Mkenv__item__instantiate_imp : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__instantiate_imp
  
let __proj__Mkenv__item__effects : env -> effects =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__effects
  
let __proj__Mkenv__item__generalize : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__generalize
  
let __proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__letrecs
  
let __proj__Mkenv__item__top_level : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__top_level
  
let __proj__Mkenv__item__check_uvars : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_uvars
  
let __proj__Mkenv__item__use_eq : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_eq
  
let __proj__Mkenv__item__is_iface : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_iface
  
let __proj__Mkenv__item__admit : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__admit
  
let __proj__Mkenv__item__lax : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax
  
let __proj__Mkenv__item__lax_universes : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax_universes
  
let __proj__Mkenv__item__failhard : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__failhard
  
let __proj__Mkenv__item__nosynth : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__nosynth
  
let __proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_term
  
let __proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__type_of
  
let __proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__universe_of
  
let __proj__Mkenv__item__use_bv_sorts : env -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_bv_sorts
  
let __proj__Mkenv__item__qname_and_index :
  env ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qname_and_index
  
let __proj__Mkenv__item__proof_ns : env -> proof_namespace =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__proof_ns
  
let __proj__Mkenv__item__synth :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth
  
let __proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_native_tactic
  
let __proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__identifier_info
  
let __proj__Mkenv__item__tc_hooks : env -> tcenv_hooks =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
  
let __proj__Mkenv__item__dsenv : env -> FStar_ToSyntax_Env.env =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dsenv
  
let __proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps =
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
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
  
let __proj__Mksolver_t__item__init : solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let __proj__Mksolver_t__item__push : solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let __proj__Mksolver_t__item__pop : solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let __proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let __proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
  
let __proj__Mksolver_t__item__preprocess :
  solver_t ->
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
  
let __proj__Mksolver_t__item__solve :
  solver_t ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let __proj__Mksolver_t__item__finish : solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let __proj__Mksolver_t__item__refresh : solver_t -> Prims.unit -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
  
let __proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
  
let __proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
  
let __proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
  
let __proj__Mkguard_t__item__implicits :
  guard_t ->
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks -> env -> binding -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
let rename_gamma :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___177_5059  ->
              match uu___177_5059 with
              | Binding_var x ->
                  let y =
                    let uu____5062 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____5062  in
                  let uu____5063 =
                    let uu____5064 = FStar_Syntax_Subst.compress y  in
                    uu____5064.FStar_Syntax_Syntax.n  in
                  (match uu____5063 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5068 =
                         let uu___191_5069 = y1  in
                         let uu____5070 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___191_5069.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___191_5069.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5070
                         }  in
                       Binding_var uu____5068
                   | uu____5073 -> failwith "Not a renaming")
              | b -> b))
  
let rename_env : FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___192_5081 = env  in
      let uu____5082 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___192_5081.solver);
        range = (uu___192_5081.range);
        curmodule = (uu___192_5081.curmodule);
        gamma = uu____5082;
        gamma_cache = (uu___192_5081.gamma_cache);
        modules = (uu___192_5081.modules);
        expected_typ = (uu___192_5081.expected_typ);
        sigtab = (uu___192_5081.sigtab);
        is_pattern = (uu___192_5081.is_pattern);
        instantiate_imp = (uu___192_5081.instantiate_imp);
        effects = (uu___192_5081.effects);
        generalize = (uu___192_5081.generalize);
        letrecs = (uu___192_5081.letrecs);
        top_level = (uu___192_5081.top_level);
        check_uvars = (uu___192_5081.check_uvars);
        use_eq = (uu___192_5081.use_eq);
        is_iface = (uu___192_5081.is_iface);
        admit = (uu___192_5081.admit);
        lax = (uu___192_5081.lax);
        lax_universes = (uu___192_5081.lax_universes);
        failhard = (uu___192_5081.failhard);
        nosynth = (uu___192_5081.nosynth);
        tc_term = (uu___192_5081.tc_term);
        type_of = (uu___192_5081.type_of);
        universe_of = (uu___192_5081.universe_of);
        use_bv_sorts = (uu___192_5081.use_bv_sorts);
        qname_and_index = (uu___192_5081.qname_and_index);
        proof_ns = (uu___192_5081.proof_ns);
        synth = (uu___192_5081.synth);
        is_native_tactic = (uu___192_5081.is_native_tactic);
        identifier_info = (uu___192_5081.identifier_info);
        tc_hooks = (uu___192_5081.tc_hooks);
        dsenv = (uu___192_5081.dsenv);
        dep_graph = (uu___192_5081.dep_graph)
      }
  
let default_tc_hooks : tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5089  -> fun uu____5090  -> ()) } 
let tc_hooks : env -> tcenv_hooks = fun env  -> env.tc_hooks 
let set_tc_hooks : env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___193_5100 = env  in
      {
        solver = (uu___193_5100.solver);
        range = (uu___193_5100.range);
        curmodule = (uu___193_5100.curmodule);
        gamma = (uu___193_5100.gamma);
        gamma_cache = (uu___193_5100.gamma_cache);
        modules = (uu___193_5100.modules);
        expected_typ = (uu___193_5100.expected_typ);
        sigtab = (uu___193_5100.sigtab);
        is_pattern = (uu___193_5100.is_pattern);
        instantiate_imp = (uu___193_5100.instantiate_imp);
        effects = (uu___193_5100.effects);
        generalize = (uu___193_5100.generalize);
        letrecs = (uu___193_5100.letrecs);
        top_level = (uu___193_5100.top_level);
        check_uvars = (uu___193_5100.check_uvars);
        use_eq = (uu___193_5100.use_eq);
        is_iface = (uu___193_5100.is_iface);
        admit = (uu___193_5100.admit);
        lax = (uu___193_5100.lax);
        lax_universes = (uu___193_5100.lax_universes);
        failhard = (uu___193_5100.failhard);
        nosynth = (uu___193_5100.nosynth);
        tc_term = (uu___193_5100.tc_term);
        type_of = (uu___193_5100.type_of);
        universe_of = (uu___193_5100.universe_of);
        use_bv_sorts = (uu___193_5100.use_bv_sorts);
        qname_and_index = (uu___193_5100.qname_and_index);
        proof_ns = (uu___193_5100.proof_ns);
        synth = (uu___193_5100.synth);
        is_native_tactic = (uu___193_5100.is_native_tactic);
        identifier_info = (uu___193_5100.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___193_5100.dsenv);
        dep_graph = (uu___193_5100.dep_graph)
      }
  
let set_dep_graph : env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___194_5107 = e  in
      {
        solver = (uu___194_5107.solver);
        range = (uu___194_5107.range);
        curmodule = (uu___194_5107.curmodule);
        gamma = (uu___194_5107.gamma);
        gamma_cache = (uu___194_5107.gamma_cache);
        modules = (uu___194_5107.modules);
        expected_typ = (uu___194_5107.expected_typ);
        sigtab = (uu___194_5107.sigtab);
        is_pattern = (uu___194_5107.is_pattern);
        instantiate_imp = (uu___194_5107.instantiate_imp);
        effects = (uu___194_5107.effects);
        generalize = (uu___194_5107.generalize);
        letrecs = (uu___194_5107.letrecs);
        top_level = (uu___194_5107.top_level);
        check_uvars = (uu___194_5107.check_uvars);
        use_eq = (uu___194_5107.use_eq);
        is_iface = (uu___194_5107.is_iface);
        admit = (uu___194_5107.admit);
        lax = (uu___194_5107.lax);
        lax_universes = (uu___194_5107.lax_universes);
        failhard = (uu___194_5107.failhard);
        nosynth = (uu___194_5107.nosynth);
        tc_term = (uu___194_5107.tc_term);
        type_of = (uu___194_5107.type_of);
        universe_of = (uu___194_5107.universe_of);
        use_bv_sorts = (uu___194_5107.use_bv_sorts);
        qname_and_index = (uu___194_5107.qname_and_index);
        proof_ns = (uu___194_5107.proof_ns);
        synth = (uu___194_5107.synth);
        is_native_tactic = (uu___194_5107.is_native_tactic);
        identifier_info = (uu___194_5107.identifier_info);
        tc_hooks = (uu___194_5107.tc_hooks);
        dsenv = (uu___194_5107.dsenv);
        dep_graph = g
      }
  
let dep_graph : env -> FStar_Parser_Dep.deps = fun e  -> e.dep_graph 
type env_t = env[@@deriving show]
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap[@@deriving show]
let should_verify : env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____5122) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5123,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5124,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5125 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab : 'Auu____5132 . Prims.unit -> 'Auu____5132 FStar_Util.smap =
  fun uu____5138  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____5141 . Prims.unit -> 'Auu____5141 FStar_Util.smap =
  fun uu____5147  -> FStar_Util.smap_create (Prims.parse_int "100") 
let initial_env :
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
          solver_t -> FStar_Ident.lident -> env
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun solver  ->
            fun module_lid  ->
              let uu____5220 = new_gamma_cache ()  in
              let uu____5223 = new_sigtab ()  in
              let uu____5226 = FStar_Options.using_facts_from ()  in
              let uu____5227 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty
                 in
              let uu____5230 = FStar_ToSyntax_Env.empty_env ()  in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5220;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5223;
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
                use_bv_sorts = false;
                qname_and_index = FStar_Pervasives_Native.None;
                proof_ns = uu____5226;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5264  -> false);
                identifier_info = uu____5227;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5230;
                dep_graph = deps
              }
  
let sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab 
let gamma_cache : env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache 
let query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]] 
let push_query_indices : Prims.unit -> Prims.unit =
  fun uu____5332  ->
    let uu____5333 = FStar_ST.op_Bang query_indices  in
    match uu____5333 with
    | [] -> failwith "Empty query indices!"
    | uu____5412 ->
        let uu____5421 =
          let uu____5430 =
            let uu____5437 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____5437  in
          let uu____5516 = FStar_ST.op_Bang query_indices  in uu____5430 ::
            uu____5516
           in
        FStar_ST.op_Colon_Equals query_indices uu____5421
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____5661  ->
    let uu____5662 = FStar_ST.op_Bang query_indices  in
    match uu____5662 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5833  ->
    match uu____5833 with
    | (l,n1) ->
        let uu____5840 = FStar_ST.op_Bang query_indices  in
        (match uu____5840 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6009 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6026  ->
    let uu____6027 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6027
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____6123 =
       let uu____6126 = FStar_ST.op_Bang stack  in env :: uu____6126  in
     FStar_ST.op_Colon_Equals stack uu____6123);
    (let uu___195_6233 = env  in
     let uu____6234 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6237 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6240 =
       let uu____6243 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6243  in
     {
       solver = (uu___195_6233.solver);
       range = (uu___195_6233.range);
       curmodule = (uu___195_6233.curmodule);
       gamma = (uu___195_6233.gamma);
       gamma_cache = uu____6234;
       modules = (uu___195_6233.modules);
       expected_typ = (uu___195_6233.expected_typ);
       sigtab = uu____6237;
       is_pattern = (uu___195_6233.is_pattern);
       instantiate_imp = (uu___195_6233.instantiate_imp);
       effects = (uu___195_6233.effects);
       generalize = (uu___195_6233.generalize);
       letrecs = (uu___195_6233.letrecs);
       top_level = (uu___195_6233.top_level);
       check_uvars = (uu___195_6233.check_uvars);
       use_eq = (uu___195_6233.use_eq);
       is_iface = (uu___195_6233.is_iface);
       admit = (uu___195_6233.admit);
       lax = (uu___195_6233.lax);
       lax_universes = (uu___195_6233.lax_universes);
       failhard = (uu___195_6233.failhard);
       nosynth = (uu___195_6233.nosynth);
       tc_term = (uu___195_6233.tc_term);
       type_of = (uu___195_6233.type_of);
       universe_of = (uu___195_6233.universe_of);
       use_bv_sorts = (uu___195_6233.use_bv_sorts);
       qname_and_index = (uu___195_6233.qname_and_index);
       proof_ns = (uu___195_6233.proof_ns);
       synth = (uu___195_6233.synth);
       is_native_tactic = (uu___195_6233.is_native_tactic);
       identifier_info = uu____6240;
       tc_hooks = (uu___195_6233.tc_hooks);
       dsenv = (uu___195_6233.dsenv);
       dep_graph = (uu___195_6233.dep_graph)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____6308  ->
    let uu____6309 = FStar_ST.op_Bang stack  in
    match uu____6309 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6421 -> failwith "Impossible: Too many pops"
  
let push : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let pop : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let incr_query_index : env -> env =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____6460 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6486  ->
                  match uu____6486 with
                  | (m,uu____6492) -> FStar_Ident.lid_equals l m))
           in
        (match uu____6460 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___196_6499 = env  in
               {
                 solver = (uu___196_6499.solver);
                 range = (uu___196_6499.range);
                 curmodule = (uu___196_6499.curmodule);
                 gamma = (uu___196_6499.gamma);
                 gamma_cache = (uu___196_6499.gamma_cache);
                 modules = (uu___196_6499.modules);
                 expected_typ = (uu___196_6499.expected_typ);
                 sigtab = (uu___196_6499.sigtab);
                 is_pattern = (uu___196_6499.is_pattern);
                 instantiate_imp = (uu___196_6499.instantiate_imp);
                 effects = (uu___196_6499.effects);
                 generalize = (uu___196_6499.generalize);
                 letrecs = (uu___196_6499.letrecs);
                 top_level = (uu___196_6499.top_level);
                 check_uvars = (uu___196_6499.check_uvars);
                 use_eq = (uu___196_6499.use_eq);
                 is_iface = (uu___196_6499.is_iface);
                 admit = (uu___196_6499.admit);
                 lax = (uu___196_6499.lax);
                 lax_universes = (uu___196_6499.lax_universes);
                 failhard = (uu___196_6499.failhard);
                 nosynth = (uu___196_6499.nosynth);
                 tc_term = (uu___196_6499.tc_term);
                 type_of = (uu___196_6499.type_of);
                 universe_of = (uu___196_6499.universe_of);
                 use_bv_sorts = (uu___196_6499.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___196_6499.proof_ns);
                 synth = (uu___196_6499.synth);
                 is_native_tactic = (uu___196_6499.is_native_tactic);
                 identifier_info = (uu___196_6499.identifier_info);
                 tc_hooks = (uu___196_6499.tc_hooks);
                 dsenv = (uu___196_6499.dsenv);
                 dep_graph = (uu___196_6499.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6504,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___197_6512 = env  in
               {
                 solver = (uu___197_6512.solver);
                 range = (uu___197_6512.range);
                 curmodule = (uu___197_6512.curmodule);
                 gamma = (uu___197_6512.gamma);
                 gamma_cache = (uu___197_6512.gamma_cache);
                 modules = (uu___197_6512.modules);
                 expected_typ = (uu___197_6512.expected_typ);
                 sigtab = (uu___197_6512.sigtab);
                 is_pattern = (uu___197_6512.is_pattern);
                 instantiate_imp = (uu___197_6512.instantiate_imp);
                 effects = (uu___197_6512.effects);
                 generalize = (uu___197_6512.generalize);
                 letrecs = (uu___197_6512.letrecs);
                 top_level = (uu___197_6512.top_level);
                 check_uvars = (uu___197_6512.check_uvars);
                 use_eq = (uu___197_6512.use_eq);
                 is_iface = (uu___197_6512.is_iface);
                 admit = (uu___197_6512.admit);
                 lax = (uu___197_6512.lax);
                 lax_universes = (uu___197_6512.lax_universes);
                 failhard = (uu___197_6512.failhard);
                 nosynth = (uu___197_6512.nosynth);
                 tc_term = (uu___197_6512.tc_term);
                 type_of = (uu___197_6512.type_of);
                 universe_of = (uu___197_6512.universe_of);
                 use_bv_sorts = (uu___197_6512.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___197_6512.proof_ns);
                 synth = (uu___197_6512.synth);
                 is_native_tactic = (uu___197_6512.is_native_tactic);
                 identifier_info = (uu___197_6512.identifier_info);
                 tc_hooks = (uu___197_6512.tc_hooks);
                 dsenv = (uu___197_6512.dsenv);
                 dep_graph = (uu___197_6512.dep_graph)
               })))
  
let debug : env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let set_range : env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___198_6530 = e  in
         {
           solver = (uu___198_6530.solver);
           range = r;
           curmodule = (uu___198_6530.curmodule);
           gamma = (uu___198_6530.gamma);
           gamma_cache = (uu___198_6530.gamma_cache);
           modules = (uu___198_6530.modules);
           expected_typ = (uu___198_6530.expected_typ);
           sigtab = (uu___198_6530.sigtab);
           is_pattern = (uu___198_6530.is_pattern);
           instantiate_imp = (uu___198_6530.instantiate_imp);
           effects = (uu___198_6530.effects);
           generalize = (uu___198_6530.generalize);
           letrecs = (uu___198_6530.letrecs);
           top_level = (uu___198_6530.top_level);
           check_uvars = (uu___198_6530.check_uvars);
           use_eq = (uu___198_6530.use_eq);
           is_iface = (uu___198_6530.is_iface);
           admit = (uu___198_6530.admit);
           lax = (uu___198_6530.lax);
           lax_universes = (uu___198_6530.lax_universes);
           failhard = (uu___198_6530.failhard);
           nosynth = (uu___198_6530.nosynth);
           tc_term = (uu___198_6530.tc_term);
           type_of = (uu___198_6530.type_of);
           universe_of = (uu___198_6530.universe_of);
           use_bv_sorts = (uu___198_6530.use_bv_sorts);
           qname_and_index = (uu___198_6530.qname_and_index);
           proof_ns = (uu___198_6530.proof_ns);
           synth = (uu___198_6530.synth);
           is_native_tactic = (uu___198_6530.is_native_tactic);
           identifier_info = (uu___198_6530.identifier_info);
           tc_hooks = (uu___198_6530.tc_hooks);
           dsenv = (uu___198_6530.dsenv);
           dep_graph = (uu___198_6530.dep_graph)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let toggle_id_info : env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6540 =
        let uu____6541 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____6541 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6540
  
let insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6647 =
          let uu____6648 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6648 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6647
  
let insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6754 =
          let uu____6755 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6755 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6754
  
let promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6863 =
        let uu____6864 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____6864 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6863
  
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___199_6975 = env  in
      {
        solver = (uu___199_6975.solver);
        range = (uu___199_6975.range);
        curmodule = lid;
        gamma = (uu___199_6975.gamma);
        gamma_cache = (uu___199_6975.gamma_cache);
        modules = (uu___199_6975.modules);
        expected_typ = (uu___199_6975.expected_typ);
        sigtab = (uu___199_6975.sigtab);
        is_pattern = (uu___199_6975.is_pattern);
        instantiate_imp = (uu___199_6975.instantiate_imp);
        effects = (uu___199_6975.effects);
        generalize = (uu___199_6975.generalize);
        letrecs = (uu___199_6975.letrecs);
        top_level = (uu___199_6975.top_level);
        check_uvars = (uu___199_6975.check_uvars);
        use_eq = (uu___199_6975.use_eq);
        is_iface = (uu___199_6975.is_iface);
        admit = (uu___199_6975.admit);
        lax = (uu___199_6975.lax);
        lax_universes = (uu___199_6975.lax_universes);
        failhard = (uu___199_6975.failhard);
        nosynth = (uu___199_6975.nosynth);
        tc_term = (uu___199_6975.tc_term);
        type_of = (uu___199_6975.type_of);
        universe_of = (uu___199_6975.universe_of);
        use_bv_sorts = (uu___199_6975.use_bv_sorts);
        qname_and_index = (uu___199_6975.qname_and_index);
        proof_ns = (uu___199_6975.proof_ns);
        synth = (uu___199_6975.synth);
        is_native_tactic = (uu___199_6975.is_native_tactic);
        identifier_info = (uu___199_6975.identifier_info);
        tc_hooks = (uu___199_6975.tc_hooks);
        dsenv = (uu___199_6975.dsenv);
        dep_graph = (uu___199_6975.dep_graph)
      }
  
let has_interface : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
  
let name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____7001 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7001)
  
let variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____7009 =
      let uu____7010 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7010  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7009)
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7013  ->
    let uu____7014 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7014
  
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____7052) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7076 = FStar_Syntax_Subst.subst vs t  in (us, uu____7076)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___178_7089  ->
    match uu___178_7089 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7113  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7126 = inst_tscheme t  in
      match uu____7126 with
      | (us,t1) ->
          let uu____7137 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7137)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7149  ->
          match uu____7149 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7164 =
                         let uu____7165 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7166 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7167 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7168 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7165 uu____7166 uu____7167 uu____7168
                          in
                       failwith uu____7164)
                    else ();
                    (let uu____7170 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7170))
               | uu____7177 ->
                   let uu____7178 =
                     let uu____7179 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7179
                      in
                   failwith uu____7178)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7183 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7187 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7191 -> false
  
let in_cur_mod : env -> FStar_Ident.lident -> tri =
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
             | ([],uu____7225) -> Maybe
             | (uu____7232,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7251 -> No  in
           aux cur1 lns)
        else No
  
let lookup_qname :
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
          let uu____7356 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7356 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___179_7401  ->
                   match uu___179_7401 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7444 =
                           let uu____7463 =
                             let uu____7478 = inst_tscheme t  in
                             FStar_Util.Inl uu____7478  in
                           (uu____7463, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7444
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7544,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7546);
                                     FStar_Syntax_Syntax.sigrng = uu____7547;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7548;
                                     FStar_Syntax_Syntax.sigmeta = uu____7549;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7550;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7570 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7570
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7616 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7623 -> cache t  in
                       let uu____7624 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7624 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7699 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7699 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7785 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7865 = find_in_sigtab env lid  in
         match uu____7865 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7964) ->
          add_sigelts env ses
      | uu____7973 ->
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
            | uu____7987 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___180_8014  ->
           match uu___180_8014 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8032 -> FStar_Pervasives_Native.None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let ((uu____8065,lb::[]),uu____8067) ->
          let uu____8080 =
            let uu____8089 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp))
               in
            let uu____8098 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname
               in
            (uu____8089, uu____8098)  in
          FStar_Pervasives_Native.Some uu____8080
      | FStar_Syntax_Syntax.Sig_let ((uu____8111,lbs),uu____8113) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8149 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8161 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____8161
                   then
                     let uu____8172 =
                       let uu____8181 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp))
                          in
                       let uu____8190 = FStar_Syntax_Syntax.range_of_fv fv
                          in
                       (uu____8181, uu____8190)  in
                     FStar_Pervasives_Native.Some uu____8172
                   else FStar_Pervasives_Native.None)
      | uu____8212 -> FStar_Pervasives_Native.None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8245 =
          let uu____8254 =
            let uu____8259 =
              let uu____8260 =
                let uu____8263 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature
                   in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8263
                 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8260)  in
            inst_tscheme uu____8259  in
          (uu____8254, (se.FStar_Syntax_Syntax.sigrng))  in
        FStar_Pervasives_Native.Some uu____8245
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8283,uu____8284) ->
        let uu____8289 =
          let uu____8298 =
            let uu____8303 =
              let uu____8304 =
                let uu____8307 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                FStar_Syntax_Util.arrow binders uu____8307  in
              (us, uu____8304)  in
            inst_tscheme uu____8303  in
          (uu____8298, (se.FStar_Syntax_Syntax.sigrng))  in
        FStar_Pervasives_Native.Some uu____8289
    | uu____8324 -> FStar_Pervasives_Native.None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____8382 =
        match uu____8382 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8478,uvs,t,uu____8481,uu____8482,uu____8483);
                    FStar_Syntax_Syntax.sigrng = uu____8484;
                    FStar_Syntax_Syntax.sigquals = uu____8485;
                    FStar_Syntax_Syntax.sigmeta = uu____8486;
                    FStar_Syntax_Syntax.sigattrs = uu____8487;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8508 =
                   let uu____8517 = inst_tscheme (uvs, t)  in
                   (uu____8517, rng)  in
                 FStar_Pervasives_Native.Some uu____8508
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8537;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8539;
                    FStar_Syntax_Syntax.sigattrs = uu____8540;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8557 =
                   let uu____8558 = in_cur_mod env l  in uu____8558 = Yes  in
                 if uu____8557
                 then
                   let uu____8569 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface
                      in
                   (if uu____8569
                    then
                      let uu____8582 =
                        let uu____8591 = inst_tscheme (uvs, t)  in
                        (uu____8591, rng)  in
                      FStar_Pervasives_Native.Some uu____8582
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8618 =
                      let uu____8627 = inst_tscheme (uvs, t)  in
                      (uu____8627, rng)  in
                    FStar_Pervasives_Native.Some uu____8618)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8648,uu____8649);
                    FStar_Syntax_Syntax.sigrng = uu____8650;
                    FStar_Syntax_Syntax.sigquals = uu____8651;
                    FStar_Syntax_Syntax.sigmeta = uu____8652;
                    FStar_Syntax_Syntax.sigattrs = uu____8653;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8692 =
                        let uu____8701 = inst_tscheme (uvs, k)  in
                        (uu____8701, rng)  in
                      FStar_Pervasives_Native.Some uu____8692
                  | uu____8718 ->
                      let uu____8719 =
                        let uu____8728 =
                          let uu____8733 =
                            let uu____8734 =
                              let uu____8737 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____8737  in
                            (uvs, uu____8734)  in
                          inst_tscheme uu____8733  in
                        (uu____8728, rng)  in
                      FStar_Pervasives_Native.Some uu____8719)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8758,uu____8759);
                    FStar_Syntax_Syntax.sigrng = uu____8760;
                    FStar_Syntax_Syntax.sigquals = uu____8761;
                    FStar_Syntax_Syntax.sigmeta = uu____8762;
                    FStar_Syntax_Syntax.sigattrs = uu____8763;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8803 =
                        let uu____8812 = inst_tscheme_with (uvs, k) us  in
                        (uu____8812, rng)  in
                      FStar_Pervasives_Native.Some uu____8803
                  | uu____8829 ->
                      let uu____8830 =
                        let uu____8839 =
                          let uu____8844 =
                            let uu____8845 =
                              let uu____8848 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____8848  in
                            (uvs, uu____8845)  in
                          inst_tscheme_with uu____8844 us  in
                        (uu____8839, rng)  in
                      FStar_Pervasives_Native.Some uu____8830)
             | FStar_Util.Inr se ->
                 let uu____8882 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8903;
                        FStar_Syntax_Syntax.sigrng = uu____8904;
                        FStar_Syntax_Syntax.sigquals = uu____8905;
                        FStar_Syntax_Syntax.sigmeta = uu____8906;
                        FStar_Syntax_Syntax.sigattrs = uu____8907;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8922 ->
                       effect_signature (FStar_Pervasives_Native.fst se)
                    in
                 FStar_All.pipe_right uu____8882
                   (FStar_Util.map_option
                      (fun uu____8970  ->
                         match uu____8970 with | (us_t,rng1) -> (us_t, rng1))))
         in
      let uu____9001 =
        let uu____9012 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____9012 mapper  in
      match uu____9001 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___200_9105 = t  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___200_9105.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___200_9105.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9130 = lookup_qname env l  in
      match uu____9130 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9169 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9217 = try_lookup_bv env bv  in
      match uu____9217 with
      | FStar_Pervasives_Native.None  ->
          let uu____9232 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9232 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9247 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9248 =
            let uu____9249 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9249  in
          (uu____9247, uu____9248)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9266 = try_lookup_lid_aux env l  in
      match uu____9266 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9332 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9332  in
          let uu____9333 =
            let uu____9342 =
              let uu____9347 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9347)  in
            (uu____9342, r1)  in
          FStar_Pervasives_Native.Some uu____9333
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9374 = try_lookup_lid env l  in
      match uu____9374 with
      | FStar_Pervasives_Native.None  ->
          let uu____9401 = name_not_found l  in
          FStar_Errors.raise_error uu____9401 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___181_9441  ->
              match uu___181_9441 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9443 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9458 = lookup_qname env lid  in
      match uu____9458 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9487,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9490;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9492;
              FStar_Syntax_Syntax.sigattrs = uu____9493;_},FStar_Pervasives_Native.None
            ),uu____9494)
          ->
          let uu____9543 =
            let uu____9554 =
              let uu____9559 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9559)  in
            (uu____9554, q)  in
          FStar_Pervasives_Native.Some uu____9543
      | uu____9576 -> FStar_Pervasives_Native.None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9613 = lookup_qname env lid  in
      match uu____9613 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9638,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9641;
              FStar_Syntax_Syntax.sigquals = uu____9642;
              FStar_Syntax_Syntax.sigmeta = uu____9643;
              FStar_Syntax_Syntax.sigattrs = uu____9644;_},FStar_Pervasives_Native.None
            ),uu____9645)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9694 ->
          let uu____9715 = name_not_found lid  in
          FStar_Errors.raise_error uu____9715 (FStar_Ident.range_of_lid lid)
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9734 = lookup_qname env lid  in
      match uu____9734 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9759,uvs,t,uu____9762,uu____9763,uu____9764);
              FStar_Syntax_Syntax.sigrng = uu____9765;
              FStar_Syntax_Syntax.sigquals = uu____9766;
              FStar_Syntax_Syntax.sigmeta = uu____9767;
              FStar_Syntax_Syntax.sigattrs = uu____9768;_},FStar_Pervasives_Native.None
            ),uu____9769)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9822 ->
          let uu____9843 = name_not_found lid  in
          FStar_Errors.raise_error uu____9843 (FStar_Ident.range_of_lid lid)
  
let datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9864 = lookup_qname env lid  in
      match uu____9864 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9891,uu____9892,uu____9893,uu____9894,uu____9895,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9897;
              FStar_Syntax_Syntax.sigquals = uu____9898;
              FStar_Syntax_Syntax.sigmeta = uu____9899;
              FStar_Syntax_Syntax.sigattrs = uu____9900;_},uu____9901),uu____9902)
          -> (true, dcs)
      | uu____9963 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9992 = lookup_qname env lid  in
      match uu____9992 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10013,uu____10014,uu____10015,l,uu____10017,uu____10018);
              FStar_Syntax_Syntax.sigrng = uu____10019;
              FStar_Syntax_Syntax.sigquals = uu____10020;
              FStar_Syntax_Syntax.sigmeta = uu____10021;
              FStar_Syntax_Syntax.sigattrs = uu____10022;_},uu____10023),uu____10024)
          -> l
      | uu____10079 ->
          let uu____10100 =
            let uu____10101 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10101  in
          failwith uu____10100
  
let lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
        let uu____10135 = lookup_qname env lid  in
        match uu____10135 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10163)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10214,lbs),uu____10216)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10244 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10244
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10276 -> FStar_Pervasives_Native.None)
        | uu____10281 -> FStar_Pervasives_Native.None
  
let try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10316 = lookup_qname env ftv  in
      match uu____10316 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10340) ->
          let uu____10385 = effect_signature se  in
          (match uu____10385 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10406,t),r) ->
               let uu____10421 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10421)
      | uu____10422 -> FStar_Pervasives_Native.None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10449 = try_lookup_effect_lid env ftv  in
      match uu____10449 with
      | FStar_Pervasives_Native.None  ->
          let uu____10452 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10452 (FStar_Ident.range_of_lid ftv)
      | FStar_Pervasives_Native.Some k -> k
  
let lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____10473 = lookup_qname env lid0  in
        match uu____10473 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10504);
                FStar_Syntax_Syntax.sigrng = uu____10505;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10507;
                FStar_Syntax_Syntax.sigattrs = uu____10508;_},FStar_Pervasives_Native.None
              ),uu____10509)
            ->
            let lid1 =
              let uu____10563 =
                let uu____10564 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10564
                 in
              FStar_Ident.set_lid_range lid uu____10563  in
            let uu____10565 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___182_10569  ->
                      match uu___182_10569 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10570 -> false))
               in
            if uu____10565
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10584 =
                      let uu____10585 =
                        let uu____10586 = get_range env  in
                        FStar_Range.string_of_range uu____10586  in
                      let uu____10587 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____10588 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10585 uu____10587 uu____10588
                       in
                    failwith uu____10584)
                  in
               match (binders, univs1) with
               | ([],uu____10595) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10612,uu____10613::uu____10614::uu____10615) ->
                   let uu____10620 =
                     let uu____10621 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____10622 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10621 uu____10622
                      in
                   failwith uu____10620
               | uu____10629 ->
                   let uu____10634 =
                     let uu____10639 =
                       let uu____10640 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____10640)  in
                     inst_tscheme_with uu____10639 insts  in
                   (match uu____10634 with
                    | (uu____10651,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____10654 =
                          let uu____10655 = FStar_Syntax_Subst.compress t1
                             in
                          uu____10655.FStar_Syntax_Syntax.n  in
                        (match uu____10654 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10702 -> failwith "Impossible")))
        | uu____10709 -> FStar_Pervasives_Native.None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10749 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____10749 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10762,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____10769 = find1 l2  in
            (match uu____10769 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____10776 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____10776 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10780 = find1 l  in
            (match uu____10780 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____10794 = lookup_qname env l1  in
      match uu____10794 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10817;
              FStar_Syntax_Syntax.sigrng = uu____10818;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10820;
              FStar_Syntax_Syntax.sigattrs = uu____10821;_},uu____10822),uu____10823)
          -> q
      | uu____10874 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10907 =
          let uu____10908 =
            let uu____10909 = FStar_Util.string_of_int i  in
            let uu____10910 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10909 uu____10910
             in
          failwith uu____10908  in
        let uu____10911 = lookup_datacon env lid  in
        match uu____10911 with
        | (uu____10916,t) ->
            let uu____10918 =
              let uu____10919 = FStar_Syntax_Subst.compress t  in
              uu____10919.FStar_Syntax_Syntax.n  in
            (match uu____10918 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10923) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____10954 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____10954
                      FStar_Pervasives_Native.fst)
             | uu____10963 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10970 = lookup_qname env l  in
      match uu____10970 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10991,uu____10992,uu____10993);
              FStar_Syntax_Syntax.sigrng = uu____10994;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10996;
              FStar_Syntax_Syntax.sigattrs = uu____10997;_},uu____10998),uu____10999)
          ->
          FStar_Util.for_some
            (fun uu___183_11052  ->
               match uu___183_11052 with
               | FStar_Syntax_Syntax.Projector uu____11053 -> true
               | uu____11058 -> false) quals
      | uu____11059 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11086 = lookup_qname env lid  in
      match uu____11086 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11107,uu____11108,uu____11109,uu____11110,uu____11111,uu____11112);
              FStar_Syntax_Syntax.sigrng = uu____11113;
              FStar_Syntax_Syntax.sigquals = uu____11114;
              FStar_Syntax_Syntax.sigmeta = uu____11115;
              FStar_Syntax_Syntax.sigattrs = uu____11116;_},uu____11117),uu____11118)
          -> true
      | uu____11173 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11200 = lookup_qname env lid  in
      match uu____11200 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11221,uu____11222,uu____11223,uu____11224,uu____11225,uu____11226);
              FStar_Syntax_Syntax.sigrng = uu____11227;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11229;
              FStar_Syntax_Syntax.sigattrs = uu____11230;_},uu____11231),uu____11232)
          ->
          FStar_Util.for_some
            (fun uu___184_11293  ->
               match uu___184_11293 with
               | FStar_Syntax_Syntax.RecordType uu____11294 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11303 -> true
               | uu____11312 -> false) quals
      | uu____11313 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11340 = lookup_qname env lid  in
      match uu____11340 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11361,uu____11362);
              FStar_Syntax_Syntax.sigrng = uu____11363;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11365;
              FStar_Syntax_Syntax.sigattrs = uu____11366;_},uu____11367),uu____11368)
          ->
          FStar_Util.for_some
            (fun uu___185_11425  ->
               match uu___185_11425 with
               | FStar_Syntax_Syntax.Action uu____11426 -> true
               | uu____11427 -> false) quals
      | uu____11428 -> false
  
let is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool =
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
      let uu____11458 =
        let uu____11459 = FStar_Syntax_Util.un_uinst head1  in
        uu____11459.FStar_Syntax_Syntax.n  in
      match uu____11458 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11463 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11528 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11544) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11561 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11568 ->
                 FStar_Pervasives_Native.Some true
             | uu____11585 -> FStar_Pervasives_Native.Some false)
         in
      let uu____11586 =
        let uu____11589 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____11589 mapper  in
      match uu____11586 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11635 = lookup_qname env lid  in
      match uu____11635 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11656,uu____11657,tps,uu____11659,uu____11660,uu____11661);
              FStar_Syntax_Syntax.sigrng = uu____11662;
              FStar_Syntax_Syntax.sigquals = uu____11663;
              FStar_Syntax_Syntax.sigmeta = uu____11664;
              FStar_Syntax_Syntax.sigattrs = uu____11665;_},uu____11666),uu____11667)
          -> FStar_List.length tps
      | uu____11730 ->
          let uu____11751 = name_not_found lid  in
          FStar_Errors.raise_error uu____11751 (FStar_Ident.range_of_lid lid)
  
let effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____11795  ->
              match uu____11795 with
              | (d,uu____11803) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11814 = effect_decl_opt env l  in
      match uu____11814 with
      | FStar_Pervasives_Native.None  ->
          let uu____11829 = name_not_found l  in
          FStar_Errors.raise_error uu____11829 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let identity_mlift : mlift =
  {
    mlift_wp = (fun uu____11855  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11870  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3
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
            (let uu____11903 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11956  ->
                       match uu____11956 with
                       | (m1,m2,uu____11969,uu____11970,uu____11971) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____11903 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11988 =
                   let uu____11993 =
                     let uu____11994 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____11995 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11994
                       uu____11995
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____11993)
                    in
                 FStar_Errors.raise_error uu____11988 env.range
             | FStar_Pervasives_Native.Some
                 (uu____12002,uu____12003,m3,j1,j2) -> (m3, j1, j2))
  
let monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
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
  'Auu____12040 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12040)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12067 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12093  ->
                match uu____12093 with
                | (d,uu____12099) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____12067 with
      | FStar_Pervasives_Native.None  ->
          let uu____12110 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12110
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12123 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12123 with
           | (uu____12134,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12144)::(wp,uu____12146)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12182 -> failwith "Impossible"))
  
let wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
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
                 let uu____12225 = get_range env  in
                 let uu____12226 =
                   let uu____12229 =
                     let uu____12230 =
                       let uu____12245 =
                         let uu____12248 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____12248]  in
                       (null_wp, uu____12245)  in
                     FStar_Syntax_Syntax.Tm_app uu____12230  in
                   FStar_Syntax_Syntax.mk uu____12229  in
                 uu____12226 FStar_Pervasives_Native.None uu____12225  in
               let uu____12254 =
                 let uu____12255 =
                   let uu____12264 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____12264]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12255;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____12254)
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___201_12273 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___201_12273.order);
              joins = (uu___201_12273.joins)
            }  in
          let uu___202_12282 = env  in
          {
            solver = (uu___202_12282.solver);
            range = (uu___202_12282.range);
            curmodule = (uu___202_12282.curmodule);
            gamma = (uu___202_12282.gamma);
            gamma_cache = (uu___202_12282.gamma_cache);
            modules = (uu___202_12282.modules);
            expected_typ = (uu___202_12282.expected_typ);
            sigtab = (uu___202_12282.sigtab);
            is_pattern = (uu___202_12282.is_pattern);
            instantiate_imp = (uu___202_12282.instantiate_imp);
            effects;
            generalize = (uu___202_12282.generalize);
            letrecs = (uu___202_12282.letrecs);
            top_level = (uu___202_12282.top_level);
            check_uvars = (uu___202_12282.check_uvars);
            use_eq = (uu___202_12282.use_eq);
            is_iface = (uu___202_12282.is_iface);
            admit = (uu___202_12282.admit);
            lax = (uu___202_12282.lax);
            lax_universes = (uu___202_12282.lax_universes);
            failhard = (uu___202_12282.failhard);
            nosynth = (uu___202_12282.nosynth);
            tc_term = (uu___202_12282.tc_term);
            type_of = (uu___202_12282.type_of);
            universe_of = (uu___202_12282.universe_of);
            use_bv_sorts = (uu___202_12282.use_bv_sorts);
            qname_and_index = (uu___202_12282.qname_and_index);
            proof_ns = (uu___202_12282.proof_ns);
            synth = (uu___202_12282.synth);
            is_native_tactic = (uu___202_12282.is_native_tactic);
            identifier_info = (uu___202_12282.identifier_info);
            tc_hooks = (uu___202_12282.tc_hooks);
            dsenv = (uu___202_12282.dsenv);
            dep_graph = (uu___202_12282.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12302 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12302  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12416 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12417 = l1 u t wp e  in
                                l2 u t uu____12416 uu____12417))
                | uu____12418 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12466 = inst_tscheme_with lift_t [u]  in
            match uu____12466 with
            | (uu____12473,lift_t1) ->
                let uu____12475 =
                  let uu____12478 =
                    let uu____12479 =
                      let uu____12494 =
                        let uu____12497 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12498 =
                          let uu____12501 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12501]  in
                        uu____12497 :: uu____12498  in
                      (lift_t1, uu____12494)  in
                    FStar_Syntax_Syntax.Tm_app uu____12479  in
                  FStar_Syntax_Syntax.mk uu____12478  in
                uu____12475 FStar_Pervasives_Native.None
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
            let uu____12551 = inst_tscheme_with lift_t [u]  in
            match uu____12551 with
            | (uu____12558,lift_t1) ->
                let uu____12560 =
                  let uu____12563 =
                    let uu____12564 =
                      let uu____12579 =
                        let uu____12582 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12583 =
                          let uu____12586 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12587 =
                            let uu____12590 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12590]  in
                          uu____12586 :: uu____12587  in
                        uu____12582 :: uu____12583  in
                      (lift_t1, uu____12579)  in
                    FStar_Syntax_Syntax.Tm_app uu____12564  in
                  FStar_Syntax_Syntax.mk uu____12563  in
                uu____12560 FStar_Pervasives_Native.None
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
              let uu____12632 =
                let uu____12633 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____12633
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____12632  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____12637 =
              let uu____12638 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____12638  in
            let uu____12639 =
              let uu____12640 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12662 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____12662)
                 in
              FStar_Util.dflt "none" uu____12640  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12637
              uu____12639
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12688  ->
                    match uu____12688 with
                    | (e,uu____12696) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____12715 =
            match uu____12715 with
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
              let uu____12753 =
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
                                    (let uu____12774 =
                                       let uu____12783 =
                                         find_edge order1 (i, k)  in
                                       let uu____12786 =
                                         find_edge order1 (k, j)  in
                                       (uu____12783, uu____12786)  in
                                     match uu____12774 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12801 =
                                           compose_edges e1 e2  in
                                         [uu____12801]
                                     | uu____12802 -> [])))))
                 in
              FStar_List.append order1 uu____12753  in
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
                   let uu____12832 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12834 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____12834
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____12832
                   then
                     let uu____12839 =
                       let uu____12844 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12844)
                        in
                     let uu____12845 = get_range env  in
                     FStar_Errors.raise_error uu____12839 uu____12845
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
                                            let uu____12970 =
                                              let uu____12979 =
                                                find_edge order2 (i, k)  in
                                              let uu____12982 =
                                                find_edge order2 (j, k)  in
                                              (uu____12979, uu____12982)  in
                                            match uu____12970 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13024,uu____13025)
                                                     ->
                                                     let uu____13032 =
                                                       let uu____13037 =
                                                         let uu____13038 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13038
                                                          in
                                                       let uu____13041 =
                                                         let uu____13042 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13042
                                                          in
                                                       (uu____13037,
                                                         uu____13041)
                                                        in
                                                     (match uu____13032 with
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
                                            | uu____13077 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___203_13150 = env.effects  in
              { decls = (uu___203_13150.decls); order = order2; joins }  in
            let uu___204_13151 = env  in
            {
              solver = (uu___204_13151.solver);
              range = (uu___204_13151.range);
              curmodule = (uu___204_13151.curmodule);
              gamma = (uu___204_13151.gamma);
              gamma_cache = (uu___204_13151.gamma_cache);
              modules = (uu___204_13151.modules);
              expected_typ = (uu___204_13151.expected_typ);
              sigtab = (uu___204_13151.sigtab);
              is_pattern = (uu___204_13151.is_pattern);
              instantiate_imp = (uu___204_13151.instantiate_imp);
              effects;
              generalize = (uu___204_13151.generalize);
              letrecs = (uu___204_13151.letrecs);
              top_level = (uu___204_13151.top_level);
              check_uvars = (uu___204_13151.check_uvars);
              use_eq = (uu___204_13151.use_eq);
              is_iface = (uu___204_13151.is_iface);
              admit = (uu___204_13151.admit);
              lax = (uu___204_13151.lax);
              lax_universes = (uu___204_13151.lax_universes);
              failhard = (uu___204_13151.failhard);
              nosynth = (uu___204_13151.nosynth);
              tc_term = (uu___204_13151.tc_term);
              type_of = (uu___204_13151.type_of);
              universe_of = (uu___204_13151.universe_of);
              use_bv_sorts = (uu___204_13151.use_bv_sorts);
              qname_and_index = (uu___204_13151.qname_and_index);
              proof_ns = (uu___204_13151.proof_ns);
              synth = (uu___204_13151.synth);
              is_native_tactic = (uu___204_13151.is_native_tactic);
              identifier_info = (uu___204_13151.identifier_info);
              tc_hooks = (uu___204_13151.tc_hooks);
              dsenv = (uu___204_13151.dsenv);
              dep_graph = (uu___204_13151.dep_graph)
            }))
      | uu____13152 -> env
  
let comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
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
        | uu____13176 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13184 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13184 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13201 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13201 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13219 =
                     let uu____13224 =
                       let uu____13225 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13230 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13237 =
                         let uu____13238 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13238  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13225 uu____13230 uu____13237
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13224)
                      in
                   FStar_Errors.raise_error uu____13219
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13243 =
                     let uu____13252 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13252 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13269  ->
                        fun uu____13270  ->
                          match (uu____13269, uu____13270) with
                          | ((x,uu____13292),(t,uu____13294)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13243
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13313 =
                     let uu___205_13314 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___205_13314.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___205_13314.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___205_13314.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___205_13314.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13313
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____13336 = effect_decl_opt env effect_name  in
          match uu____13336 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13369 =
                only_reifiable &&
                  (let uu____13371 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13371)
                 in
              if uu____13369
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13387 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13406 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13435 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13435
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13436 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13436
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13446 =
                       let uu____13449 = get_range env  in
                       let uu____13450 =
                         let uu____13453 =
                           let uu____13454 =
                             let uu____13469 =
                               let uu____13472 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13472; wp]  in
                             (repr, uu____13469)  in
                           FStar_Syntax_Syntax.Tm_app uu____13454  in
                         FStar_Syntax_Syntax.mk uu____13453  in
                       uu____13450 FStar_Pervasives_Native.None uu____13449
                        in
                     FStar_Pervasives_Native.Some uu____13446)
  
let effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____13518 =
            let uu____13523 =
              let uu____13524 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13524
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13523)  in
          let uu____13525 = get_range env  in
          FStar_Errors.raise_error uu____13518 uu____13525  in
        let uu____13526 = effect_repr_aux true env c u_c  in
        match uu____13526 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
  
let is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let is_reifiable : env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____13560 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13567 =
        let uu____13568 = FStar_Syntax_Subst.compress t  in
        uu____13568.FStar_Syntax_Syntax.n  in
      match uu____13567 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13571,c) ->
          is_reifiable_comp env c
      | uu____13589 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13611)::uu____13612 -> x :: rest
        | (Binding_sig_inst uu____13621)::uu____13622 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13637 = push1 x rest1  in local :: uu____13637
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___206_13641 = env  in
       let uu____13642 = push1 s env.gamma  in
       {
         solver = (uu___206_13641.solver);
         range = (uu___206_13641.range);
         curmodule = (uu___206_13641.curmodule);
         gamma = uu____13642;
         gamma_cache = (uu___206_13641.gamma_cache);
         modules = (uu___206_13641.modules);
         expected_typ = (uu___206_13641.expected_typ);
         sigtab = (uu___206_13641.sigtab);
         is_pattern = (uu___206_13641.is_pattern);
         instantiate_imp = (uu___206_13641.instantiate_imp);
         effects = (uu___206_13641.effects);
         generalize = (uu___206_13641.generalize);
         letrecs = (uu___206_13641.letrecs);
         top_level = (uu___206_13641.top_level);
         check_uvars = (uu___206_13641.check_uvars);
         use_eq = (uu___206_13641.use_eq);
         is_iface = (uu___206_13641.is_iface);
         admit = (uu___206_13641.admit);
         lax = (uu___206_13641.lax);
         lax_universes = (uu___206_13641.lax_universes);
         failhard = (uu___206_13641.failhard);
         nosynth = (uu___206_13641.nosynth);
         tc_term = (uu___206_13641.tc_term);
         type_of = (uu___206_13641.type_of);
         universe_of = (uu___206_13641.universe_of);
         use_bv_sorts = (uu___206_13641.use_bv_sorts);
         qname_and_index = (uu___206_13641.qname_and_index);
         proof_ns = (uu___206_13641.proof_ns);
         synth = (uu___206_13641.synth);
         is_native_tactic = (uu___206_13641.is_native_tactic);
         identifier_info = (uu___206_13641.identifier_info);
         tc_hooks = (uu___206_13641.tc_hooks);
         dsenv = (uu___206_13641.dsenv);
         dep_graph = (uu___206_13641.dep_graph)
       })
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
         in
      build_lattice env1 s
  
let push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
           in
        build_lattice env1 s
  
let push_local_binding : env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___207_13672 = env  in
      {
        solver = (uu___207_13672.solver);
        range = (uu___207_13672.range);
        curmodule = (uu___207_13672.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___207_13672.gamma_cache);
        modules = (uu___207_13672.modules);
        expected_typ = (uu___207_13672.expected_typ);
        sigtab = (uu___207_13672.sigtab);
        is_pattern = (uu___207_13672.is_pattern);
        instantiate_imp = (uu___207_13672.instantiate_imp);
        effects = (uu___207_13672.effects);
        generalize = (uu___207_13672.generalize);
        letrecs = (uu___207_13672.letrecs);
        top_level = (uu___207_13672.top_level);
        check_uvars = (uu___207_13672.check_uvars);
        use_eq = (uu___207_13672.use_eq);
        is_iface = (uu___207_13672.is_iface);
        admit = (uu___207_13672.admit);
        lax = (uu___207_13672.lax);
        lax_universes = (uu___207_13672.lax_universes);
        failhard = (uu___207_13672.failhard);
        nosynth = (uu___207_13672.nosynth);
        tc_term = (uu___207_13672.tc_term);
        type_of = (uu___207_13672.type_of);
        universe_of = (uu___207_13672.universe_of);
        use_bv_sorts = (uu___207_13672.use_bv_sorts);
        qname_and_index = (uu___207_13672.qname_and_index);
        proof_ns = (uu___207_13672.proof_ns);
        synth = (uu___207_13672.synth);
        is_native_tactic = (uu___207_13672.is_native_tactic);
        identifier_info = (uu___207_13672.identifier_info);
        tc_hooks = (uu___207_13672.tc_hooks);
        dsenv = (uu___207_13672.dsenv);
        dep_graph = (uu___207_13672.dep_graph)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___208_13703 = env  in
             {
               solver = (uu___208_13703.solver);
               range = (uu___208_13703.range);
               curmodule = (uu___208_13703.curmodule);
               gamma = rest;
               gamma_cache = (uu___208_13703.gamma_cache);
               modules = (uu___208_13703.modules);
               expected_typ = (uu___208_13703.expected_typ);
               sigtab = (uu___208_13703.sigtab);
               is_pattern = (uu___208_13703.is_pattern);
               instantiate_imp = (uu___208_13703.instantiate_imp);
               effects = (uu___208_13703.effects);
               generalize = (uu___208_13703.generalize);
               letrecs = (uu___208_13703.letrecs);
               top_level = (uu___208_13703.top_level);
               check_uvars = (uu___208_13703.check_uvars);
               use_eq = (uu___208_13703.use_eq);
               is_iface = (uu___208_13703.is_iface);
               admit = (uu___208_13703.admit);
               lax = (uu___208_13703.lax);
               lax_universes = (uu___208_13703.lax_universes);
               failhard = (uu___208_13703.failhard);
               nosynth = (uu___208_13703.nosynth);
               tc_term = (uu___208_13703.tc_term);
               type_of = (uu___208_13703.type_of);
               universe_of = (uu___208_13703.universe_of);
               use_bv_sorts = (uu___208_13703.use_bv_sorts);
               qname_and_index = (uu___208_13703.qname_and_index);
               proof_ns = (uu___208_13703.proof_ns);
               synth = (uu___208_13703.synth);
               is_native_tactic = (uu___208_13703.is_native_tactic);
               identifier_info = (uu___208_13703.identifier_info);
               tc_hooks = (uu___208_13703.tc_hooks);
               dsenv = (uu___208_13703.dsenv);
               dep_graph = (uu___208_13703.dep_graph)
             }))
    | uu____13704 -> FStar_Pervasives_Native.None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13726  ->
             match uu____13726 with | (x,uu____13732) -> push_bv env1 x) env
        bs
  
let binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___209_13760 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___209_13760.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___209_13760.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let push_module : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___210_13790 = env  in
       {
         solver = (uu___210_13790.solver);
         range = (uu___210_13790.range);
         curmodule = (uu___210_13790.curmodule);
         gamma = [];
         gamma_cache = (uu___210_13790.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___210_13790.sigtab);
         is_pattern = (uu___210_13790.is_pattern);
         instantiate_imp = (uu___210_13790.instantiate_imp);
         effects = (uu___210_13790.effects);
         generalize = (uu___210_13790.generalize);
         letrecs = (uu___210_13790.letrecs);
         top_level = (uu___210_13790.top_level);
         check_uvars = (uu___210_13790.check_uvars);
         use_eq = (uu___210_13790.use_eq);
         is_iface = (uu___210_13790.is_iface);
         admit = (uu___210_13790.admit);
         lax = (uu___210_13790.lax);
         lax_universes = (uu___210_13790.lax_universes);
         failhard = (uu___210_13790.failhard);
         nosynth = (uu___210_13790.nosynth);
         tc_term = (uu___210_13790.tc_term);
         type_of = (uu___210_13790.type_of);
         universe_of = (uu___210_13790.universe_of);
         use_bv_sorts = (uu___210_13790.use_bv_sorts);
         qname_and_index = (uu___210_13790.qname_and_index);
         proof_ns = (uu___210_13790.proof_ns);
         synth = (uu___210_13790.synth);
         is_native_tactic = (uu___210_13790.is_native_tactic);
         identifier_info = (uu___210_13790.identifier_info);
         tc_hooks = (uu___210_13790.tc_hooks);
         dsenv = (uu___210_13790.dsenv);
         dep_graph = (uu___210_13790.dep_graph)
       })
  
let push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
  
let open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____13822 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____13822 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____13850 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____13850)
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___211_13863 = env  in
      {
        solver = (uu___211_13863.solver);
        range = (uu___211_13863.range);
        curmodule = (uu___211_13863.curmodule);
        gamma = (uu___211_13863.gamma);
        gamma_cache = (uu___211_13863.gamma_cache);
        modules = (uu___211_13863.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___211_13863.sigtab);
        is_pattern = (uu___211_13863.is_pattern);
        instantiate_imp = (uu___211_13863.instantiate_imp);
        effects = (uu___211_13863.effects);
        generalize = (uu___211_13863.generalize);
        letrecs = (uu___211_13863.letrecs);
        top_level = (uu___211_13863.top_level);
        check_uvars = (uu___211_13863.check_uvars);
        use_eq = false;
        is_iface = (uu___211_13863.is_iface);
        admit = (uu___211_13863.admit);
        lax = (uu___211_13863.lax);
        lax_universes = (uu___211_13863.lax_universes);
        failhard = (uu___211_13863.failhard);
        nosynth = (uu___211_13863.nosynth);
        tc_term = (uu___211_13863.tc_term);
        type_of = (uu___211_13863.type_of);
        universe_of = (uu___211_13863.universe_of);
        use_bv_sorts = (uu___211_13863.use_bv_sorts);
        qname_and_index = (uu___211_13863.qname_and_index);
        proof_ns = (uu___211_13863.proof_ns);
        synth = (uu___211_13863.synth);
        is_native_tactic = (uu___211_13863.is_native_tactic);
        identifier_info = (uu___211_13863.identifier_info);
        tc_hooks = (uu___211_13863.tc_hooks);
        dsenv = (uu___211_13863.dsenv);
        dep_graph = (uu___211_13863.dep_graph)
      }
  
let expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let clear_expected_typ :
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun env_  ->
    let uu____13887 = expected_typ env_  in
    ((let uu___212_13893 = env_  in
      {
        solver = (uu___212_13893.solver);
        range = (uu___212_13893.range);
        curmodule = (uu___212_13893.curmodule);
        gamma = (uu___212_13893.gamma);
        gamma_cache = (uu___212_13893.gamma_cache);
        modules = (uu___212_13893.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___212_13893.sigtab);
        is_pattern = (uu___212_13893.is_pattern);
        instantiate_imp = (uu___212_13893.instantiate_imp);
        effects = (uu___212_13893.effects);
        generalize = (uu___212_13893.generalize);
        letrecs = (uu___212_13893.letrecs);
        top_level = (uu___212_13893.top_level);
        check_uvars = (uu___212_13893.check_uvars);
        use_eq = false;
        is_iface = (uu___212_13893.is_iface);
        admit = (uu___212_13893.admit);
        lax = (uu___212_13893.lax);
        lax_universes = (uu___212_13893.lax_universes);
        failhard = (uu___212_13893.failhard);
        nosynth = (uu___212_13893.nosynth);
        tc_term = (uu___212_13893.tc_term);
        type_of = (uu___212_13893.type_of);
        universe_of = (uu___212_13893.universe_of);
        use_bv_sorts = (uu___212_13893.use_bv_sorts);
        qname_and_index = (uu___212_13893.qname_and_index);
        proof_ns = (uu___212_13893.proof_ns);
        synth = (uu___212_13893.synth);
        is_native_tactic = (uu___212_13893.is_native_tactic);
        identifier_info = (uu___212_13893.identifier_info);
        tc_hooks = (uu___212_13893.tc_hooks);
        dsenv = (uu___212_13893.dsenv);
        dep_graph = (uu___212_13893.dep_graph)
      }), uu____13887)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13906 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___186_13916  ->
                    match uu___186_13916 with
                    | Binding_sig (uu____13919,se) -> [se]
                    | uu____13925 -> []))
             in
          FStar_All.pipe_right uu____13906 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___213_13932 = env  in
       {
         solver = (uu___213_13932.solver);
         range = (uu___213_13932.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___213_13932.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___213_13932.expected_typ);
         sigtab = (uu___213_13932.sigtab);
         is_pattern = (uu___213_13932.is_pattern);
         instantiate_imp = (uu___213_13932.instantiate_imp);
         effects = (uu___213_13932.effects);
         generalize = (uu___213_13932.generalize);
         letrecs = (uu___213_13932.letrecs);
         top_level = (uu___213_13932.top_level);
         check_uvars = (uu___213_13932.check_uvars);
         use_eq = (uu___213_13932.use_eq);
         is_iface = (uu___213_13932.is_iface);
         admit = (uu___213_13932.admit);
         lax = (uu___213_13932.lax);
         lax_universes = (uu___213_13932.lax_universes);
         failhard = (uu___213_13932.failhard);
         nosynth = (uu___213_13932.nosynth);
         tc_term = (uu___213_13932.tc_term);
         type_of = (uu___213_13932.type_of);
         universe_of = (uu___213_13932.universe_of);
         use_bv_sorts = (uu___213_13932.use_bv_sorts);
         qname_and_index = (uu___213_13932.qname_and_index);
         proof_ns = (uu___213_13932.proof_ns);
         synth = (uu___213_13932.synth);
         is_native_tactic = (uu___213_13932.is_native_tactic);
         identifier_info = (uu___213_13932.identifier_info);
         tc_hooks = (uu___213_13932.tc_hooks);
         dsenv = (uu___213_13932.dsenv);
         dep_graph = (uu___213_13932.dep_graph)
       })
  
let uvars_in_env : env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14013)::tl1 -> aux out tl1
      | (Binding_lid (uu____14017,(uu____14018,t)))::tl1 ->
          let uu____14033 =
            let uu____14040 = FStar_Syntax_Free.uvars t  in
            ext out uu____14040  in
          aux uu____14033 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14047;
            FStar_Syntax_Syntax.index = uu____14048;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14055 =
            let uu____14062 = FStar_Syntax_Free.uvars t  in
            ext out uu____14062  in
          aux uu____14055 tl1
      | (Binding_sig uu____14069)::uu____14070 -> out
      | (Binding_sig_inst uu____14079)::uu____14080 -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14135)::tl1 -> aux out tl1
      | (Binding_univ uu____14147)::tl1 -> aux out tl1
      | (Binding_lid (uu____14151,(uu____14152,t)))::tl1 ->
          let uu____14167 =
            let uu____14170 = FStar_Syntax_Free.univs t  in
            ext out uu____14170  in
          aux uu____14167 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14173;
            FStar_Syntax_Syntax.index = uu____14174;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14181 =
            let uu____14184 = FStar_Syntax_Free.univs t  in
            ext out uu____14184  in
          aux uu____14181 tl1
      | (Binding_sig uu____14187)::uu____14188 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14241)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14257 = FStar_Util.fifo_set_add uname out  in
          aux uu____14257 tl1
      | (Binding_lid (uu____14260,(uu____14261,t)))::tl1 ->
          let uu____14276 =
            let uu____14279 = FStar_Syntax_Free.univnames t  in
            ext out uu____14279  in
          aux uu____14276 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14282;
            FStar_Syntax_Syntax.index = uu____14283;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14290 =
            let uu____14293 = FStar_Syntax_Free.univnames t  in
            ext out uu____14293  in
          aux uu____14290 tl1
      | (Binding_sig uu____14296)::uu____14297 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___187_14321  ->
            match uu___187_14321 with
            | Binding_var x -> [x]
            | Binding_lid uu____14325 -> []
            | Binding_sig uu____14330 -> []
            | Binding_univ uu____14337 -> []
            | Binding_sig_inst uu____14338 -> []))
  
let binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14354 =
      let uu____14357 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14357
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14354 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____14379 =
      let uu____14380 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___188_14390  ->
                match uu___188_14390 with
                | Binding_var x ->
                    let uu____14392 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14392
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14395) ->
                    let uu____14396 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14396
                | Binding_sig (ls,uu____14398) ->
                    let uu____14403 =
                      let uu____14404 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14404
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14403
                | Binding_sig_inst (ls,uu____14414,uu____14415) ->
                    let uu____14420 =
                      let uu____14421 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14421
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14420))
         in
      FStar_All.pipe_right uu____14380 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14379 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14438 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14438
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14466  ->
                 fun uu____14467  ->
                   match (uu____14466, uu____14467) with
                   | ((b1,uu____14485),(b2,uu____14487)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let string_of_delta_level : delta_level -> Prims.string =
  fun uu___189_14529  ->
    match uu___189_14529 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14530 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___190_14548  ->
             match uu___190_14548 with
             | Binding_sig (lids,uu____14554) -> FStar_List.append lids keys
             | uu____14559 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14565  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let should_enc_path : env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14599) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14618,uu____14619) -> false  in
      let uu____14628 =
        FStar_List.tryFind
          (fun uu____14646  ->
             match uu____14646 with | (p,uu____14654) -> list_prefix p path)
          env.proof_ns
         in
      match uu____14628 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14665,b) -> b
  
let should_enc_lid : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14683 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____14683
  
let cons_proof_ns : Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___214_14695 = e  in
        {
          solver = (uu___214_14695.solver);
          range = (uu___214_14695.range);
          curmodule = (uu___214_14695.curmodule);
          gamma = (uu___214_14695.gamma);
          gamma_cache = (uu___214_14695.gamma_cache);
          modules = (uu___214_14695.modules);
          expected_typ = (uu___214_14695.expected_typ);
          sigtab = (uu___214_14695.sigtab);
          is_pattern = (uu___214_14695.is_pattern);
          instantiate_imp = (uu___214_14695.instantiate_imp);
          effects = (uu___214_14695.effects);
          generalize = (uu___214_14695.generalize);
          letrecs = (uu___214_14695.letrecs);
          top_level = (uu___214_14695.top_level);
          check_uvars = (uu___214_14695.check_uvars);
          use_eq = (uu___214_14695.use_eq);
          is_iface = (uu___214_14695.is_iface);
          admit = (uu___214_14695.admit);
          lax = (uu___214_14695.lax);
          lax_universes = (uu___214_14695.lax_universes);
          failhard = (uu___214_14695.failhard);
          nosynth = (uu___214_14695.nosynth);
          tc_term = (uu___214_14695.tc_term);
          type_of = (uu___214_14695.type_of);
          universe_of = (uu___214_14695.universe_of);
          use_bv_sorts = (uu___214_14695.use_bv_sorts);
          qname_and_index = (uu___214_14695.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___214_14695.synth);
          is_native_tactic = (uu___214_14695.is_native_tactic);
          identifier_info = (uu___214_14695.identifier_info);
          tc_hooks = (uu___214_14695.tc_hooks);
          dsenv = (uu___214_14695.dsenv);
          dep_graph = (uu___214_14695.dep_graph)
        }
  
let add_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path 
let rem_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path 
let get_proof_ns : env -> proof_namespace = fun e  -> e.proof_ns 
let set_proof_ns : proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___215_14721 = e  in
      {
        solver = (uu___215_14721.solver);
        range = (uu___215_14721.range);
        curmodule = (uu___215_14721.curmodule);
        gamma = (uu___215_14721.gamma);
        gamma_cache = (uu___215_14721.gamma_cache);
        modules = (uu___215_14721.modules);
        expected_typ = (uu___215_14721.expected_typ);
        sigtab = (uu___215_14721.sigtab);
        is_pattern = (uu___215_14721.is_pattern);
        instantiate_imp = (uu___215_14721.instantiate_imp);
        effects = (uu___215_14721.effects);
        generalize = (uu___215_14721.generalize);
        letrecs = (uu___215_14721.letrecs);
        top_level = (uu___215_14721.top_level);
        check_uvars = (uu___215_14721.check_uvars);
        use_eq = (uu___215_14721.use_eq);
        is_iface = (uu___215_14721.is_iface);
        admit = (uu___215_14721.admit);
        lax = (uu___215_14721.lax);
        lax_universes = (uu___215_14721.lax_universes);
        failhard = (uu___215_14721.failhard);
        nosynth = (uu___215_14721.nosynth);
        tc_term = (uu___215_14721.tc_term);
        type_of = (uu___215_14721.type_of);
        universe_of = (uu___215_14721.universe_of);
        use_bv_sorts = (uu___215_14721.use_bv_sorts);
        qname_and_index = (uu___215_14721.qname_and_index);
        proof_ns = ns;
        synth = (uu___215_14721.synth);
        is_native_tactic = (uu___215_14721.is_native_tactic);
        identifier_info = (uu___215_14721.identifier_info);
        tc_hooks = (uu___215_14721.tc_hooks);
        dsenv = (uu___215_14721.dsenv);
        dep_graph = (uu___215_14721.dep_graph)
      }
  
let unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14732 = FStar_Syntax_Free.names t  in
      let uu____14735 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14732 uu____14735
  
let closed : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14752 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____14752
  
let closed' : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14758 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____14758
  
let string_of_proof_ns : env -> Prims.string =
  fun env  ->
    let aux uu____14773 =
      match uu____14773 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14789 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____14789)
       in
    let uu____14791 =
      let uu____14794 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____14794 FStar_List.rev  in
    FStar_All.pipe_right uu____14791 (FStar_String.concat " ")
  
let dummy_solver : solver_t =
  {
    init = (fun uu____14811  -> ());
    push = (fun uu____14813  -> ());
    pop = (fun uu____14815  -> ());
    encode_modul = (fun uu____14818  -> fun uu____14819  -> ());
    encode_sig = (fun uu____14822  -> fun uu____14823  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14829 =
             let uu____14836 = FStar_Options.peek ()  in (e, g, uu____14836)
              in
           [uu____14829]);
    solve = (fun uu____14852  -> fun uu____14853  -> fun uu____14854  -> ());
    finish = (fun uu____14860  -> ());
    refresh = (fun uu____14862  -> ())
  } 