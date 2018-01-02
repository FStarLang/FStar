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
           (fun uu___69_5079  ->
              match uu___69_5079 with
              | Binding_var x ->
                  let y =
                    let uu____5082 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____5082  in
                  let uu____5083 =
                    let uu____5084 = FStar_Syntax_Subst.compress y  in
                    uu____5084.FStar_Syntax_Syntax.n  in
                  (match uu____5083 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5088 =
                         let uu___84_5089 = y1  in
                         let uu____5090 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___84_5089.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___84_5089.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5090
                         }  in
                       Binding_var uu____5088
                   | uu____5093 -> failwith "Not a renaming")
              | b -> b))
  
let rename_env : FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___85_5101 = env  in
      let uu____5102 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___85_5101.solver);
        range = (uu___85_5101.range);
        curmodule = (uu___85_5101.curmodule);
        gamma = uu____5102;
        gamma_cache = (uu___85_5101.gamma_cache);
        modules = (uu___85_5101.modules);
        expected_typ = (uu___85_5101.expected_typ);
        sigtab = (uu___85_5101.sigtab);
        is_pattern = (uu___85_5101.is_pattern);
        instantiate_imp = (uu___85_5101.instantiate_imp);
        effects = (uu___85_5101.effects);
        generalize = (uu___85_5101.generalize);
        letrecs = (uu___85_5101.letrecs);
        top_level = (uu___85_5101.top_level);
        check_uvars = (uu___85_5101.check_uvars);
        use_eq = (uu___85_5101.use_eq);
        is_iface = (uu___85_5101.is_iface);
        admit = (uu___85_5101.admit);
        lax = (uu___85_5101.lax);
        lax_universes = (uu___85_5101.lax_universes);
        failhard = (uu___85_5101.failhard);
        nosynth = (uu___85_5101.nosynth);
        tc_term = (uu___85_5101.tc_term);
        type_of = (uu___85_5101.type_of);
        universe_of = (uu___85_5101.universe_of);
        use_bv_sorts = (uu___85_5101.use_bv_sorts);
        qname_and_index = (uu___85_5101.qname_and_index);
        proof_ns = (uu___85_5101.proof_ns);
        synth = (uu___85_5101.synth);
        is_native_tactic = (uu___85_5101.is_native_tactic);
        identifier_info = (uu___85_5101.identifier_info);
        tc_hooks = (uu___85_5101.tc_hooks);
        dsenv = (uu___85_5101.dsenv);
        dep_graph = (uu___85_5101.dep_graph)
      }
  
let default_tc_hooks : tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5109  -> fun uu____5110  -> ()) } 
let tc_hooks : env -> tcenv_hooks = fun env  -> env.tc_hooks 
let set_tc_hooks : env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___86_5120 = env  in
      {
        solver = (uu___86_5120.solver);
        range = (uu___86_5120.range);
        curmodule = (uu___86_5120.curmodule);
        gamma = (uu___86_5120.gamma);
        gamma_cache = (uu___86_5120.gamma_cache);
        modules = (uu___86_5120.modules);
        expected_typ = (uu___86_5120.expected_typ);
        sigtab = (uu___86_5120.sigtab);
        is_pattern = (uu___86_5120.is_pattern);
        instantiate_imp = (uu___86_5120.instantiate_imp);
        effects = (uu___86_5120.effects);
        generalize = (uu___86_5120.generalize);
        letrecs = (uu___86_5120.letrecs);
        top_level = (uu___86_5120.top_level);
        check_uvars = (uu___86_5120.check_uvars);
        use_eq = (uu___86_5120.use_eq);
        is_iface = (uu___86_5120.is_iface);
        admit = (uu___86_5120.admit);
        lax = (uu___86_5120.lax);
        lax_universes = (uu___86_5120.lax_universes);
        failhard = (uu___86_5120.failhard);
        nosynth = (uu___86_5120.nosynth);
        tc_term = (uu___86_5120.tc_term);
        type_of = (uu___86_5120.type_of);
        universe_of = (uu___86_5120.universe_of);
        use_bv_sorts = (uu___86_5120.use_bv_sorts);
        qname_and_index = (uu___86_5120.qname_and_index);
        proof_ns = (uu___86_5120.proof_ns);
        synth = (uu___86_5120.synth);
        is_native_tactic = (uu___86_5120.is_native_tactic);
        identifier_info = (uu___86_5120.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___86_5120.dsenv);
        dep_graph = (uu___86_5120.dep_graph)
      }
  
let set_dep_graph : env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___87_5127 = e  in
      {
        solver = (uu___87_5127.solver);
        range = (uu___87_5127.range);
        curmodule = (uu___87_5127.curmodule);
        gamma = (uu___87_5127.gamma);
        gamma_cache = (uu___87_5127.gamma_cache);
        modules = (uu___87_5127.modules);
        expected_typ = (uu___87_5127.expected_typ);
        sigtab = (uu___87_5127.sigtab);
        is_pattern = (uu___87_5127.is_pattern);
        instantiate_imp = (uu___87_5127.instantiate_imp);
        effects = (uu___87_5127.effects);
        generalize = (uu___87_5127.generalize);
        letrecs = (uu___87_5127.letrecs);
        top_level = (uu___87_5127.top_level);
        check_uvars = (uu___87_5127.check_uvars);
        use_eq = (uu___87_5127.use_eq);
        is_iface = (uu___87_5127.is_iface);
        admit = (uu___87_5127.admit);
        lax = (uu___87_5127.lax);
        lax_universes = (uu___87_5127.lax_universes);
        failhard = (uu___87_5127.failhard);
        nosynth = (uu___87_5127.nosynth);
        tc_term = (uu___87_5127.tc_term);
        type_of = (uu___87_5127.type_of);
        universe_of = (uu___87_5127.universe_of);
        use_bv_sorts = (uu___87_5127.use_bv_sorts);
        qname_and_index = (uu___87_5127.qname_and_index);
        proof_ns = (uu___87_5127.proof_ns);
        synth = (uu___87_5127.synth);
        is_native_tactic = (uu___87_5127.is_native_tactic);
        identifier_info = (uu___87_5127.identifier_info);
        tc_hooks = (uu___87_5127.tc_hooks);
        dsenv = (uu___87_5127.dsenv);
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
      | (NoDelta ,uu____5142) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5143,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5144,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5145 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab : 'Auu____5152 . Prims.unit -> 'Auu____5152 FStar_Util.smap =
  fun uu____5158  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____5161 . Prims.unit -> 'Auu____5161 FStar_Util.smap =
  fun uu____5167  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
              let uu____5240 = new_gamma_cache ()  in
              let uu____5243 = new_sigtab ()  in
              let uu____5246 = FStar_Options.using_facts_from ()  in
              let uu____5247 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty
                 in
              let uu____5250 = FStar_ToSyntax_Env.empty_env ()  in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5240;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5243;
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
                proof_ns = uu____5246;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5284  -> false);
                identifier_info = uu____5247;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5250;
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
  fun uu____5364  ->
    let uu____5365 = FStar_ST.op_Bang query_indices  in
    match uu____5365 with
    | [] -> failwith "Empty query indices!"
    | uu____5444 ->
        let uu____5453 =
          let uu____5462 =
            let uu____5469 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____5469  in
          let uu____5548 = FStar_ST.op_Bang query_indices  in uu____5462 ::
            uu____5548
           in
        FStar_ST.op_Colon_Equals query_indices uu____5453
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____5693  ->
    let uu____5694 = FStar_ST.op_Bang query_indices  in
    match uu____5694 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5865  ->
    match uu____5865 with
    | (l,n1) ->
        let uu____5872 = FStar_ST.op_Bang query_indices  in
        (match uu____5872 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6041 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6058  ->
    let uu____6059 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6059
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____6159 =
       let uu____6162 = FStar_ST.op_Bang stack  in env :: uu____6162  in
     FStar_ST.op_Colon_Equals stack uu____6159);
    (let uu___88_6269 = env  in
     let uu____6270 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6273 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6276 =
       let uu____6279 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6279  in
     {
       solver = (uu___88_6269.solver);
       range = (uu___88_6269.range);
       curmodule = (uu___88_6269.curmodule);
       gamma = (uu___88_6269.gamma);
       gamma_cache = uu____6270;
       modules = (uu___88_6269.modules);
       expected_typ = (uu___88_6269.expected_typ);
       sigtab = uu____6273;
       is_pattern = (uu___88_6269.is_pattern);
       instantiate_imp = (uu___88_6269.instantiate_imp);
       effects = (uu___88_6269.effects);
       generalize = (uu___88_6269.generalize);
       letrecs = (uu___88_6269.letrecs);
       top_level = (uu___88_6269.top_level);
       check_uvars = (uu___88_6269.check_uvars);
       use_eq = (uu___88_6269.use_eq);
       is_iface = (uu___88_6269.is_iface);
       admit = (uu___88_6269.admit);
       lax = (uu___88_6269.lax);
       lax_universes = (uu___88_6269.lax_universes);
       failhard = (uu___88_6269.failhard);
       nosynth = (uu___88_6269.nosynth);
       tc_term = (uu___88_6269.tc_term);
       type_of = (uu___88_6269.type_of);
       universe_of = (uu___88_6269.universe_of);
       use_bv_sorts = (uu___88_6269.use_bv_sorts);
       qname_and_index = (uu___88_6269.qname_and_index);
       proof_ns = (uu___88_6269.proof_ns);
       synth = (uu___88_6269.synth);
       is_native_tactic = (uu___88_6269.is_native_tactic);
       identifier_info = uu____6276;
       tc_hooks = (uu___88_6269.tc_hooks);
       dsenv = (uu___88_6269.dsenv);
       dep_graph = (uu___88_6269.dep_graph)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____6352  ->
    let uu____6353 = FStar_ST.op_Bang stack  in
    match uu____6353 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6465 -> failwith "Impossible: Too many pops"
  
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
        let uu____6504 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6530  ->
                  match uu____6530 with
                  | (m,uu____6536) -> FStar_Ident.lid_equals l m))
           in
        (match uu____6504 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___89_6543 = env  in
               {
                 solver = (uu___89_6543.solver);
                 range = (uu___89_6543.range);
                 curmodule = (uu___89_6543.curmodule);
                 gamma = (uu___89_6543.gamma);
                 gamma_cache = (uu___89_6543.gamma_cache);
                 modules = (uu___89_6543.modules);
                 expected_typ = (uu___89_6543.expected_typ);
                 sigtab = (uu___89_6543.sigtab);
                 is_pattern = (uu___89_6543.is_pattern);
                 instantiate_imp = (uu___89_6543.instantiate_imp);
                 effects = (uu___89_6543.effects);
                 generalize = (uu___89_6543.generalize);
                 letrecs = (uu___89_6543.letrecs);
                 top_level = (uu___89_6543.top_level);
                 check_uvars = (uu___89_6543.check_uvars);
                 use_eq = (uu___89_6543.use_eq);
                 is_iface = (uu___89_6543.is_iface);
                 admit = (uu___89_6543.admit);
                 lax = (uu___89_6543.lax);
                 lax_universes = (uu___89_6543.lax_universes);
                 failhard = (uu___89_6543.failhard);
                 nosynth = (uu___89_6543.nosynth);
                 tc_term = (uu___89_6543.tc_term);
                 type_of = (uu___89_6543.type_of);
                 universe_of = (uu___89_6543.universe_of);
                 use_bv_sorts = (uu___89_6543.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___89_6543.proof_ns);
                 synth = (uu___89_6543.synth);
                 is_native_tactic = (uu___89_6543.is_native_tactic);
                 identifier_info = (uu___89_6543.identifier_info);
                 tc_hooks = (uu___89_6543.tc_hooks);
                 dsenv = (uu___89_6543.dsenv);
                 dep_graph = (uu___89_6543.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6548,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___90_6556 = env  in
               {
                 solver = (uu___90_6556.solver);
                 range = (uu___90_6556.range);
                 curmodule = (uu___90_6556.curmodule);
                 gamma = (uu___90_6556.gamma);
                 gamma_cache = (uu___90_6556.gamma_cache);
                 modules = (uu___90_6556.modules);
                 expected_typ = (uu___90_6556.expected_typ);
                 sigtab = (uu___90_6556.sigtab);
                 is_pattern = (uu___90_6556.is_pattern);
                 instantiate_imp = (uu___90_6556.instantiate_imp);
                 effects = (uu___90_6556.effects);
                 generalize = (uu___90_6556.generalize);
                 letrecs = (uu___90_6556.letrecs);
                 top_level = (uu___90_6556.top_level);
                 check_uvars = (uu___90_6556.check_uvars);
                 use_eq = (uu___90_6556.use_eq);
                 is_iface = (uu___90_6556.is_iface);
                 admit = (uu___90_6556.admit);
                 lax = (uu___90_6556.lax);
                 lax_universes = (uu___90_6556.lax_universes);
                 failhard = (uu___90_6556.failhard);
                 nosynth = (uu___90_6556.nosynth);
                 tc_term = (uu___90_6556.tc_term);
                 type_of = (uu___90_6556.type_of);
                 universe_of = (uu___90_6556.universe_of);
                 use_bv_sorts = (uu___90_6556.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___90_6556.proof_ns);
                 synth = (uu___90_6556.synth);
                 is_native_tactic = (uu___90_6556.is_native_tactic);
                 identifier_info = (uu___90_6556.identifier_info);
                 tc_hooks = (uu___90_6556.tc_hooks);
                 dsenv = (uu___90_6556.dsenv);
                 dep_graph = (uu___90_6556.dep_graph)
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
        (let uu___91_6574 = e  in
         {
           solver = (uu___91_6574.solver);
           range = r;
           curmodule = (uu___91_6574.curmodule);
           gamma = (uu___91_6574.gamma);
           gamma_cache = (uu___91_6574.gamma_cache);
           modules = (uu___91_6574.modules);
           expected_typ = (uu___91_6574.expected_typ);
           sigtab = (uu___91_6574.sigtab);
           is_pattern = (uu___91_6574.is_pattern);
           instantiate_imp = (uu___91_6574.instantiate_imp);
           effects = (uu___91_6574.effects);
           generalize = (uu___91_6574.generalize);
           letrecs = (uu___91_6574.letrecs);
           top_level = (uu___91_6574.top_level);
           check_uvars = (uu___91_6574.check_uvars);
           use_eq = (uu___91_6574.use_eq);
           is_iface = (uu___91_6574.is_iface);
           admit = (uu___91_6574.admit);
           lax = (uu___91_6574.lax);
           lax_universes = (uu___91_6574.lax_universes);
           failhard = (uu___91_6574.failhard);
           nosynth = (uu___91_6574.nosynth);
           tc_term = (uu___91_6574.tc_term);
           type_of = (uu___91_6574.type_of);
           universe_of = (uu___91_6574.universe_of);
           use_bv_sorts = (uu___91_6574.use_bv_sorts);
           qname_and_index = (uu___91_6574.qname_and_index);
           proof_ns = (uu___91_6574.proof_ns);
           synth = (uu___91_6574.synth);
           is_native_tactic = (uu___91_6574.is_native_tactic);
           identifier_info = (uu___91_6574.identifier_info);
           tc_hooks = (uu___91_6574.tc_hooks);
           dsenv = (uu___91_6574.dsenv);
           dep_graph = (uu___91_6574.dep_graph)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let toggle_id_info : env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6584 =
        let uu____6585 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____6585 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6584
  
let insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6691 =
          let uu____6692 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6692 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6691
  
let insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6798 =
          let uu____6799 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6799 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6798
  
let promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6907 =
        let uu____6908 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____6908 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6907
  
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___92_7019 = env  in
      {
        solver = (uu___92_7019.solver);
        range = (uu___92_7019.range);
        curmodule = lid;
        gamma = (uu___92_7019.gamma);
        gamma_cache = (uu___92_7019.gamma_cache);
        modules = (uu___92_7019.modules);
        expected_typ = (uu___92_7019.expected_typ);
        sigtab = (uu___92_7019.sigtab);
        is_pattern = (uu___92_7019.is_pattern);
        instantiate_imp = (uu___92_7019.instantiate_imp);
        effects = (uu___92_7019.effects);
        generalize = (uu___92_7019.generalize);
        letrecs = (uu___92_7019.letrecs);
        top_level = (uu___92_7019.top_level);
        check_uvars = (uu___92_7019.check_uvars);
        use_eq = (uu___92_7019.use_eq);
        is_iface = (uu___92_7019.is_iface);
        admit = (uu___92_7019.admit);
        lax = (uu___92_7019.lax);
        lax_universes = (uu___92_7019.lax_universes);
        failhard = (uu___92_7019.failhard);
        nosynth = (uu___92_7019.nosynth);
        tc_term = (uu___92_7019.tc_term);
        type_of = (uu___92_7019.type_of);
        universe_of = (uu___92_7019.universe_of);
        use_bv_sorts = (uu___92_7019.use_bv_sorts);
        qname_and_index = (uu___92_7019.qname_and_index);
        proof_ns = (uu___92_7019.proof_ns);
        synth = (uu___92_7019.synth);
        is_native_tactic = (uu___92_7019.is_native_tactic);
        identifier_info = (uu___92_7019.identifier_info);
        tc_hooks = (uu___92_7019.tc_hooks);
        dsenv = (uu___92_7019.dsenv);
        dep_graph = (uu___92_7019.dep_graph)
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
    let uu____7045 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7045)
  
let variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____7053 =
      let uu____7054 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7054  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7053)
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7057  ->
    let uu____7058 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7058
  
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
      | ((formals,t),uu____7096) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7120 = FStar_Syntax_Subst.subst vs t  in (us, uu____7120)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___70_7133  ->
    match uu___70_7133 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7157  -> new_u_univ ()))
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
      let uu____7170 = inst_tscheme t  in
      match uu____7170 with
      | (us,t1) ->
          let uu____7181 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7181)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7193  ->
          match uu____7193 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7208 =
                         let uu____7209 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7210 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7211 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7212 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7209 uu____7210 uu____7211 uu____7212
                          in
                       failwith uu____7208)
                    else ();
                    (let uu____7214 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7214))
               | uu____7221 ->
                   let uu____7222 =
                     let uu____7223 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7223
                      in
                   failwith uu____7222)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7227 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7231 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7235 -> false
  
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
             | ([],uu____7269) -> Maybe
             | (uu____7276,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7295 -> No  in
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
          let uu____7400 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7400 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___71_7445  ->
                   match uu___71_7445 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7488 =
                           let uu____7507 =
                             let uu____7522 = inst_tscheme t  in
                             FStar_Util.Inl uu____7522  in
                           (uu____7507, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7488
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7588,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7590);
                                     FStar_Syntax_Syntax.sigrng = uu____7591;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7592;
                                     FStar_Syntax_Syntax.sigmeta = uu____7593;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7594;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7614 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7614
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7660 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7667 -> cache t  in
                       let uu____7668 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7668 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7743 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7743 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7829 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7909 = find_in_sigtab env lid  in
         match uu____7909 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8008) ->
          add_sigelts env ses
      | uu____8017 ->
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
            | uu____8031 -> ()))

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
        (fun uu___72_8058  ->
           match uu___72_8058 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8076 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.Sig_let ((uu____8109,lb::[]),uu____8111) ->
          let uu____8124 =
            let uu____8133 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp))
               in
            let uu____8142 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname
               in
            (uu____8133, uu____8142)  in
          FStar_Pervasives_Native.Some uu____8124
      | FStar_Syntax_Syntax.Sig_let ((uu____8155,lbs),uu____8157) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8193 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8205 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____8205
                   then
                     let uu____8216 =
                       let uu____8225 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp))
                          in
                       let uu____8234 = FStar_Syntax_Syntax.range_of_fv fv
                          in
                       (uu____8225, uu____8234)  in
                     FStar_Pervasives_Native.Some uu____8216
                   else FStar_Pervasives_Native.None)
      | uu____8256 -> FStar_Pervasives_Native.None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8289 =
          let uu____8298 =
            let uu____8303 =
              let uu____8304 =
                let uu____8307 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature
                   in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8307
                 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8304)  in
            inst_tscheme uu____8303  in
          (uu____8298, (se.FStar_Syntax_Syntax.sigrng))  in
        FStar_Pervasives_Native.Some uu____8289
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8327,uu____8328) ->
        let uu____8333 =
          let uu____8342 =
            let uu____8347 =
              let uu____8348 =
                let uu____8351 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                FStar_Syntax_Util.arrow binders uu____8351  in
              (us, uu____8348)  in
            inst_tscheme uu____8347  in
          (uu____8342, (se.FStar_Syntax_Syntax.sigrng))  in
        FStar_Pervasives_Native.Some uu____8333
    | uu____8368 -> FStar_Pervasives_Native.None
  
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
      let mapper uu____8426 =
        match uu____8426 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8522,uvs,t,uu____8525,uu____8526,uu____8527);
                    FStar_Syntax_Syntax.sigrng = uu____8528;
                    FStar_Syntax_Syntax.sigquals = uu____8529;
                    FStar_Syntax_Syntax.sigmeta = uu____8530;
                    FStar_Syntax_Syntax.sigattrs = uu____8531;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8552 =
                   let uu____8561 = inst_tscheme (uvs, t)  in
                   (uu____8561, rng)  in
                 FStar_Pervasives_Native.Some uu____8552
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8581;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8583;
                    FStar_Syntax_Syntax.sigattrs = uu____8584;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8601 =
                   let uu____8602 = in_cur_mod env l  in uu____8602 = Yes  in
                 if uu____8601
                 then
                   let uu____8613 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface
                      in
                   (if uu____8613
                    then
                      let uu____8626 =
                        let uu____8635 = inst_tscheme (uvs, t)  in
                        (uu____8635, rng)  in
                      FStar_Pervasives_Native.Some uu____8626
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8662 =
                      let uu____8671 = inst_tscheme (uvs, t)  in
                      (uu____8671, rng)  in
                    FStar_Pervasives_Native.Some uu____8662)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8692,uu____8693);
                    FStar_Syntax_Syntax.sigrng = uu____8694;
                    FStar_Syntax_Syntax.sigquals = uu____8695;
                    FStar_Syntax_Syntax.sigmeta = uu____8696;
                    FStar_Syntax_Syntax.sigattrs = uu____8697;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8736 =
                        let uu____8745 = inst_tscheme (uvs, k)  in
                        (uu____8745, rng)  in
                      FStar_Pervasives_Native.Some uu____8736
                  | uu____8762 ->
                      let uu____8763 =
                        let uu____8772 =
                          let uu____8777 =
                            let uu____8778 =
                              let uu____8781 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____8781  in
                            (uvs, uu____8778)  in
                          inst_tscheme uu____8777  in
                        (uu____8772, rng)  in
                      FStar_Pervasives_Native.Some uu____8763)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8802,uu____8803);
                    FStar_Syntax_Syntax.sigrng = uu____8804;
                    FStar_Syntax_Syntax.sigquals = uu____8805;
                    FStar_Syntax_Syntax.sigmeta = uu____8806;
                    FStar_Syntax_Syntax.sigattrs = uu____8807;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8847 =
                        let uu____8856 = inst_tscheme_with (uvs, k) us  in
                        (uu____8856, rng)  in
                      FStar_Pervasives_Native.Some uu____8847
                  | uu____8873 ->
                      let uu____8874 =
                        let uu____8883 =
                          let uu____8888 =
                            let uu____8889 =
                              let uu____8892 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____8892  in
                            (uvs, uu____8889)  in
                          inst_tscheme_with uu____8888 us  in
                        (uu____8883, rng)  in
                      FStar_Pervasives_Native.Some uu____8874)
             | FStar_Util.Inr se ->
                 let uu____8926 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8947;
                        FStar_Syntax_Syntax.sigrng = uu____8948;
                        FStar_Syntax_Syntax.sigquals = uu____8949;
                        FStar_Syntax_Syntax.sigmeta = uu____8950;
                        FStar_Syntax_Syntax.sigattrs = uu____8951;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8966 ->
                       effect_signature (FStar_Pervasives_Native.fst se)
                    in
                 FStar_All.pipe_right uu____8926
                   (FStar_Util.map_option
                      (fun uu____9014  ->
                         match uu____9014 with | (us_t,rng1) -> (us_t, rng1))))
         in
      let uu____9045 =
        let uu____9056 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____9056 mapper  in
      match uu____9045 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___93_9149 = t  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___93_9149.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___93_9149.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9174 = lookup_qname env l  in
      match uu____9174 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9213 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9261 = try_lookup_bv env bv  in
      match uu____9261 with
      | FStar_Pervasives_Native.None  ->
          let uu____9276 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9276 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9291 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9292 =
            let uu____9293 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9293  in
          (uu____9291, uu____9292)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9310 = try_lookup_lid_aux env l  in
      match uu____9310 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9376 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9376  in
          let uu____9377 =
            let uu____9386 =
              let uu____9391 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9391)  in
            (uu____9386, r1)  in
          FStar_Pervasives_Native.Some uu____9377
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9418 = try_lookup_lid env l  in
      match uu____9418 with
      | FStar_Pervasives_Native.None  ->
          let uu____9445 = name_not_found l  in
          FStar_Errors.raise_error uu____9445 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___73_9485  ->
              match uu___73_9485 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9487 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9502 = lookup_qname env lid  in
      match uu____9502 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9531,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9534;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9536;
              FStar_Syntax_Syntax.sigattrs = uu____9537;_},FStar_Pervasives_Native.None
            ),uu____9538)
          ->
          let uu____9587 =
            let uu____9598 =
              let uu____9603 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9603)  in
            (uu____9598, q)  in
          FStar_Pervasives_Native.Some uu____9587
      | uu____9620 -> FStar_Pervasives_Native.None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9657 = lookup_qname env lid  in
      match uu____9657 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9682,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9685;
              FStar_Syntax_Syntax.sigquals = uu____9686;
              FStar_Syntax_Syntax.sigmeta = uu____9687;
              FStar_Syntax_Syntax.sigattrs = uu____9688;_},FStar_Pervasives_Native.None
            ),uu____9689)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9738 ->
          let uu____9759 = name_not_found lid  in
          FStar_Errors.raise_error uu____9759 (FStar_Ident.range_of_lid lid)
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9778 = lookup_qname env lid  in
      match uu____9778 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9803,uvs,t,uu____9806,uu____9807,uu____9808);
              FStar_Syntax_Syntax.sigrng = uu____9809;
              FStar_Syntax_Syntax.sigquals = uu____9810;
              FStar_Syntax_Syntax.sigmeta = uu____9811;
              FStar_Syntax_Syntax.sigattrs = uu____9812;_},FStar_Pervasives_Native.None
            ),uu____9813)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9866 ->
          let uu____9887 = name_not_found lid  in
          FStar_Errors.raise_error uu____9887 (FStar_Ident.range_of_lid lid)
  
let datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9908 = lookup_qname env lid  in
      match uu____9908 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9935,uu____9936,uu____9937,uu____9938,uu____9939,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9941;
              FStar_Syntax_Syntax.sigquals = uu____9942;
              FStar_Syntax_Syntax.sigmeta = uu____9943;
              FStar_Syntax_Syntax.sigattrs = uu____9944;_},uu____9945),uu____9946)
          -> (true, dcs)
      | uu____10007 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____10036 = lookup_qname env lid  in
      match uu____10036 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10057,uu____10058,uu____10059,l,uu____10061,uu____10062);
              FStar_Syntax_Syntax.sigrng = uu____10063;
              FStar_Syntax_Syntax.sigquals = uu____10064;
              FStar_Syntax_Syntax.sigmeta = uu____10065;
              FStar_Syntax_Syntax.sigattrs = uu____10066;_},uu____10067),uu____10068)
          -> l
      | uu____10123 ->
          let uu____10144 =
            let uu____10145 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10145  in
          failwith uu____10144
  
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
        let uu____10179 = lookup_qname env lid  in
        match uu____10179 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10207)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10258,lbs),uu____10260)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10288 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10288
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10320 -> FStar_Pervasives_Native.None)
        | uu____10325 -> FStar_Pervasives_Native.None
  
let try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10360 = lookup_qname env ftv  in
      match uu____10360 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10384) ->
          let uu____10429 = effect_signature se  in
          (match uu____10429 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10450,t),r) ->
               let uu____10465 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10465)
      | uu____10466 -> FStar_Pervasives_Native.None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10493 = try_lookup_effect_lid env ftv  in
      match uu____10493 with
      | FStar_Pervasives_Native.None  ->
          let uu____10496 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10496 (FStar_Ident.range_of_lid ftv)
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
        let uu____10517 = lookup_qname env lid0  in
        match uu____10517 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10548);
                FStar_Syntax_Syntax.sigrng = uu____10549;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10551;
                FStar_Syntax_Syntax.sigattrs = uu____10552;_},FStar_Pervasives_Native.None
              ),uu____10553)
            ->
            let lid1 =
              let uu____10607 =
                let uu____10608 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10608
                 in
              FStar_Ident.set_lid_range lid uu____10607  in
            let uu____10609 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___74_10613  ->
                      match uu___74_10613 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10614 -> false))
               in
            if uu____10609
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10628 =
                      let uu____10629 =
                        let uu____10630 = get_range env  in
                        FStar_Range.string_of_range uu____10630  in
                      let uu____10631 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____10632 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10629 uu____10631 uu____10632
                       in
                    failwith uu____10628)
                  in
               match (binders, univs1) with
               | ([],uu____10639) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10656,uu____10657::uu____10658::uu____10659) ->
                   let uu____10664 =
                     let uu____10665 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____10666 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10665 uu____10666
                      in
                   failwith uu____10664
               | uu____10673 ->
                   let uu____10678 =
                     let uu____10683 =
                       let uu____10684 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____10684)  in
                     inst_tscheme_with uu____10683 insts  in
                   (match uu____10678 with
                    | (uu____10695,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____10698 =
                          let uu____10699 = FStar_Syntax_Subst.compress t1
                             in
                          uu____10699.FStar_Syntax_Syntax.n  in
                        (match uu____10698 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10746 -> failwith "Impossible")))
        | uu____10753 -> FStar_Pervasives_Native.None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10793 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____10793 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10806,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____10813 = find1 l2  in
            (match uu____10813 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____10820 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____10820 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10824 = find1 l  in
            (match uu____10824 with
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
      let uu____10838 = lookup_qname env l1  in
      match uu____10838 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10861;
              FStar_Syntax_Syntax.sigrng = uu____10862;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10864;
              FStar_Syntax_Syntax.sigattrs = uu____10865;_},uu____10866),uu____10867)
          -> q
      | uu____10918 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10951 =
          let uu____10952 =
            let uu____10953 = FStar_Util.string_of_int i  in
            let uu____10954 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10953 uu____10954
             in
          failwith uu____10952  in
        let uu____10955 = lookup_datacon env lid  in
        match uu____10955 with
        | (uu____10960,t) ->
            let uu____10962 =
              let uu____10963 = FStar_Syntax_Subst.compress t  in
              uu____10963.FStar_Syntax_Syntax.n  in
            (match uu____10962 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10967) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____10998 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____10998
                      FStar_Pervasives_Native.fst)
             | uu____11007 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11014 = lookup_qname env l  in
      match uu____11014 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11035,uu____11036,uu____11037);
              FStar_Syntax_Syntax.sigrng = uu____11038;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11040;
              FStar_Syntax_Syntax.sigattrs = uu____11041;_},uu____11042),uu____11043)
          ->
          FStar_Util.for_some
            (fun uu___75_11096  ->
               match uu___75_11096 with
               | FStar_Syntax_Syntax.Projector uu____11097 -> true
               | uu____11102 -> false) quals
      | uu____11103 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11130 = lookup_qname env lid  in
      match uu____11130 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11151,uu____11152,uu____11153,uu____11154,uu____11155,uu____11156);
              FStar_Syntax_Syntax.sigrng = uu____11157;
              FStar_Syntax_Syntax.sigquals = uu____11158;
              FStar_Syntax_Syntax.sigmeta = uu____11159;
              FStar_Syntax_Syntax.sigattrs = uu____11160;_},uu____11161),uu____11162)
          -> true
      | uu____11217 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11244 = lookup_qname env lid  in
      match uu____11244 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11265,uu____11266,uu____11267,uu____11268,uu____11269,uu____11270);
              FStar_Syntax_Syntax.sigrng = uu____11271;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11273;
              FStar_Syntax_Syntax.sigattrs = uu____11274;_},uu____11275),uu____11276)
          ->
          FStar_Util.for_some
            (fun uu___76_11337  ->
               match uu___76_11337 with
               | FStar_Syntax_Syntax.RecordType uu____11338 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11347 -> true
               | uu____11356 -> false) quals
      | uu____11357 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11384 = lookup_qname env lid  in
      match uu____11384 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11405,uu____11406);
              FStar_Syntax_Syntax.sigrng = uu____11407;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11409;
              FStar_Syntax_Syntax.sigattrs = uu____11410;_},uu____11411),uu____11412)
          ->
          FStar_Util.for_some
            (fun uu___77_11469  ->
               match uu___77_11469 with
               | FStar_Syntax_Syntax.Action uu____11470 -> true
               | uu____11471 -> false) quals
      | uu____11472 -> false
  
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
      let uu____11502 =
        let uu____11503 = FStar_Syntax_Util.un_uinst head1  in
        uu____11503.FStar_Syntax_Syntax.n  in
      match uu____11502 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11507 -> false
  
let is_irreducible : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11514 = lookup_qname env l  in
      match uu____11514 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11536),uu____11537) ->
          FStar_Util.for_some
            (fun uu___78_11585  ->
               match uu___78_11585 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11586 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11587 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11672 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11688) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11705 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11712 ->
                 FStar_Pervasives_Native.Some true
             | uu____11729 -> FStar_Pervasives_Native.Some false)
         in
      let uu____11730 =
        let uu____11733 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____11733 mapper  in
      match uu____11730 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11779 = lookup_qname env lid  in
      match uu____11779 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11800,uu____11801,tps,uu____11803,uu____11804,uu____11805);
              FStar_Syntax_Syntax.sigrng = uu____11806;
              FStar_Syntax_Syntax.sigquals = uu____11807;
              FStar_Syntax_Syntax.sigmeta = uu____11808;
              FStar_Syntax_Syntax.sigattrs = uu____11809;_},uu____11810),uu____11811)
          -> FStar_List.length tps
      | uu____11874 ->
          let uu____11895 = name_not_found lid  in
          FStar_Errors.raise_error uu____11895 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____11939  ->
              match uu____11939 with
              | (d,uu____11947) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11958 = effect_decl_opt env l  in
      match uu____11958 with
      | FStar_Pervasives_Native.None  ->
          let uu____11973 = name_not_found l  in
          FStar_Errors.raise_error uu____11973 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let identity_mlift : mlift =
  {
    mlift_wp = (fun uu____11999  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____12014  ->
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
            (let uu____12047 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____12100  ->
                       match uu____12100 with
                       | (m1,m2,uu____12113,uu____12114,uu____12115) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____12047 with
             | FStar_Pervasives_Native.None  ->
                 let uu____12132 =
                   let uu____12137 =
                     let uu____12138 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____12139 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____12138
                       uu____12139
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____12137)
                    in
                 FStar_Errors.raise_error uu____12132 env.range
             | FStar_Pervasives_Native.Some
                 (uu____12146,uu____12147,m3,j1,j2) -> (m3, j1, j2))
  
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
  'Auu____12184 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12184)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12211 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12237  ->
                match uu____12237 with
                | (d,uu____12243) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____12211 with
      | FStar_Pervasives_Native.None  ->
          let uu____12254 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12254
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12267 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12267 with
           | (uu____12278,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12288)::(wp,uu____12290)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12326 -> failwith "Impossible"))
  
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
                 let uu____12369 = get_range env  in
                 let uu____12370 =
                   let uu____12373 =
                     let uu____12374 =
                       let uu____12389 =
                         let uu____12392 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____12392]  in
                       (null_wp, uu____12389)  in
                     FStar_Syntax_Syntax.Tm_app uu____12374  in
                   FStar_Syntax_Syntax.mk uu____12373  in
                 uu____12370 FStar_Pervasives_Native.None uu____12369  in
               let uu____12398 =
                 let uu____12399 =
                   let uu____12408 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____12408]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12399;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____12398)
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___94_12417 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___94_12417.order);
              joins = (uu___94_12417.joins)
            }  in
          let uu___95_12426 = env  in
          {
            solver = (uu___95_12426.solver);
            range = (uu___95_12426.range);
            curmodule = (uu___95_12426.curmodule);
            gamma = (uu___95_12426.gamma);
            gamma_cache = (uu___95_12426.gamma_cache);
            modules = (uu___95_12426.modules);
            expected_typ = (uu___95_12426.expected_typ);
            sigtab = (uu___95_12426.sigtab);
            is_pattern = (uu___95_12426.is_pattern);
            instantiate_imp = (uu___95_12426.instantiate_imp);
            effects;
            generalize = (uu___95_12426.generalize);
            letrecs = (uu___95_12426.letrecs);
            top_level = (uu___95_12426.top_level);
            check_uvars = (uu___95_12426.check_uvars);
            use_eq = (uu___95_12426.use_eq);
            is_iface = (uu___95_12426.is_iface);
            admit = (uu___95_12426.admit);
            lax = (uu___95_12426.lax);
            lax_universes = (uu___95_12426.lax_universes);
            failhard = (uu___95_12426.failhard);
            nosynth = (uu___95_12426.nosynth);
            tc_term = (uu___95_12426.tc_term);
            type_of = (uu___95_12426.type_of);
            universe_of = (uu___95_12426.universe_of);
            use_bv_sorts = (uu___95_12426.use_bv_sorts);
            qname_and_index = (uu___95_12426.qname_and_index);
            proof_ns = (uu___95_12426.proof_ns);
            synth = (uu___95_12426.synth);
            is_native_tactic = (uu___95_12426.is_native_tactic);
            identifier_info = (uu___95_12426.identifier_info);
            tc_hooks = (uu___95_12426.tc_hooks);
            dsenv = (uu___95_12426.dsenv);
            dep_graph = (uu___95_12426.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12446 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12446  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12560 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12561 = l1 u t wp e  in
                                l2 u t uu____12560 uu____12561))
                | uu____12562 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12610 = inst_tscheme_with lift_t [u]  in
            match uu____12610 with
            | (uu____12617,lift_t1) ->
                let uu____12619 =
                  let uu____12622 =
                    let uu____12623 =
                      let uu____12638 =
                        let uu____12641 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12642 =
                          let uu____12645 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12645]  in
                        uu____12641 :: uu____12642  in
                      (lift_t1, uu____12638)  in
                    FStar_Syntax_Syntax.Tm_app uu____12623  in
                  FStar_Syntax_Syntax.mk uu____12622  in
                uu____12619 FStar_Pervasives_Native.None
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
            let uu____12695 = inst_tscheme_with lift_t [u]  in
            match uu____12695 with
            | (uu____12702,lift_t1) ->
                let uu____12704 =
                  let uu____12707 =
                    let uu____12708 =
                      let uu____12723 =
                        let uu____12726 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12727 =
                          let uu____12730 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12731 =
                            let uu____12734 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12734]  in
                          uu____12730 :: uu____12731  in
                        uu____12726 :: uu____12727  in
                      (lift_t1, uu____12723)  in
                    FStar_Syntax_Syntax.Tm_app uu____12708  in
                  FStar_Syntax_Syntax.mk uu____12707  in
                uu____12704 FStar_Pervasives_Native.None
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
              let uu____12776 =
                let uu____12777 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____12777
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____12776  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____12781 =
              let uu____12782 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____12782  in
            let uu____12783 =
              let uu____12784 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12806 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____12806)
                 in
              FStar_Util.dflt "none" uu____12784  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12781
              uu____12783
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12832  ->
                    match uu____12832 with
                    | (e,uu____12840) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____12859 =
            match uu____12859 with
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
              let uu____12897 =
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
                                    (let uu____12918 =
                                       let uu____12927 =
                                         find_edge order1 (i, k)  in
                                       let uu____12930 =
                                         find_edge order1 (k, j)  in
                                       (uu____12927, uu____12930)  in
                                     match uu____12918 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12945 =
                                           compose_edges e1 e2  in
                                         [uu____12945]
                                     | uu____12946 -> [])))))
                 in
              FStar_List.append order1 uu____12897  in
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
                   let uu____12976 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12978 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____12978
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____12976
                   then
                     let uu____12983 =
                       let uu____12988 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12988)
                        in
                     let uu____12989 = get_range env  in
                     FStar_Errors.raise_error uu____12983 uu____12989
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
                                            let uu____13114 =
                                              let uu____13123 =
                                                find_edge order2 (i, k)  in
                                              let uu____13126 =
                                                find_edge order2 (j, k)  in
                                              (uu____13123, uu____13126)  in
                                            match uu____13114 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13168,uu____13169)
                                                     ->
                                                     let uu____13176 =
                                                       let uu____13181 =
                                                         let uu____13182 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13182
                                                          in
                                                       let uu____13185 =
                                                         let uu____13186 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13186
                                                          in
                                                       (uu____13181,
                                                         uu____13185)
                                                        in
                                                     (match uu____13176 with
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
                                            | uu____13221 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___96_13294 = env.effects  in
              { decls = (uu___96_13294.decls); order = order2; joins }  in
            let uu___97_13295 = env  in
            {
              solver = (uu___97_13295.solver);
              range = (uu___97_13295.range);
              curmodule = (uu___97_13295.curmodule);
              gamma = (uu___97_13295.gamma);
              gamma_cache = (uu___97_13295.gamma_cache);
              modules = (uu___97_13295.modules);
              expected_typ = (uu___97_13295.expected_typ);
              sigtab = (uu___97_13295.sigtab);
              is_pattern = (uu___97_13295.is_pattern);
              instantiate_imp = (uu___97_13295.instantiate_imp);
              effects;
              generalize = (uu___97_13295.generalize);
              letrecs = (uu___97_13295.letrecs);
              top_level = (uu___97_13295.top_level);
              check_uvars = (uu___97_13295.check_uvars);
              use_eq = (uu___97_13295.use_eq);
              is_iface = (uu___97_13295.is_iface);
              admit = (uu___97_13295.admit);
              lax = (uu___97_13295.lax);
              lax_universes = (uu___97_13295.lax_universes);
              failhard = (uu___97_13295.failhard);
              nosynth = (uu___97_13295.nosynth);
              tc_term = (uu___97_13295.tc_term);
              type_of = (uu___97_13295.type_of);
              universe_of = (uu___97_13295.universe_of);
              use_bv_sorts = (uu___97_13295.use_bv_sorts);
              qname_and_index = (uu___97_13295.qname_and_index);
              proof_ns = (uu___97_13295.proof_ns);
              synth = (uu___97_13295.synth);
              is_native_tactic = (uu___97_13295.is_native_tactic);
              identifier_info = (uu___97_13295.identifier_info);
              tc_hooks = (uu___97_13295.tc_hooks);
              dsenv = (uu___97_13295.dsenv);
              dep_graph = (uu___97_13295.dep_graph)
            }))
      | uu____13296 -> env
  
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
        | uu____13320 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13328 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13328 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13345 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13345 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13363 =
                     let uu____13368 =
                       let uu____13369 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13374 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13381 =
                         let uu____13382 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13382  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13369 uu____13374 uu____13381
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13368)
                      in
                   FStar_Errors.raise_error uu____13363
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13387 =
                     let uu____13396 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13396 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13413  ->
                        fun uu____13414  ->
                          match (uu____13413, uu____13414) with
                          | ((x,uu____13436),(t,uu____13438)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13387
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13457 =
                     let uu___98_13458 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___98_13458.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___98_13458.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___98_13458.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___98_13458.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13457
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
          let uu____13480 = effect_decl_opt env effect_name  in
          match uu____13480 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13513 =
                only_reifiable &&
                  (let uu____13515 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13515)
                 in
              if uu____13513
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13531 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13550 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13579 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13579
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13580 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13580
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13590 =
                       let uu____13593 = get_range env  in
                       let uu____13594 =
                         let uu____13597 =
                           let uu____13598 =
                             let uu____13613 =
                               let uu____13616 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13616; wp]  in
                             (repr, uu____13613)  in
                           FStar_Syntax_Syntax.Tm_app uu____13598  in
                         FStar_Syntax_Syntax.mk uu____13597  in
                       uu____13594 FStar_Pervasives_Native.None uu____13593
                        in
                     FStar_Pervasives_Native.Some uu____13590)
  
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
          let uu____13662 =
            let uu____13667 =
              let uu____13668 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13668
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13667)  in
          let uu____13669 = get_range env  in
          FStar_Errors.raise_error uu____13662 uu____13669  in
        let uu____13670 = effect_repr_aux true env c u_c  in
        match uu____13670 with
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
      | uu____13704 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13711 =
        let uu____13712 = FStar_Syntax_Subst.compress t  in
        uu____13712.FStar_Syntax_Syntax.n  in
      match uu____13711 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13715,c) ->
          is_reifiable_comp env c
      | uu____13733 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13755)::uu____13756 -> x :: rest
        | (Binding_sig_inst uu____13765)::uu____13766 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13781 = push1 x rest1  in local :: uu____13781
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___99_13785 = env  in
       let uu____13786 = push1 s env.gamma  in
       {
         solver = (uu___99_13785.solver);
         range = (uu___99_13785.range);
         curmodule = (uu___99_13785.curmodule);
         gamma = uu____13786;
         gamma_cache = (uu___99_13785.gamma_cache);
         modules = (uu___99_13785.modules);
         expected_typ = (uu___99_13785.expected_typ);
         sigtab = (uu___99_13785.sigtab);
         is_pattern = (uu___99_13785.is_pattern);
         instantiate_imp = (uu___99_13785.instantiate_imp);
         effects = (uu___99_13785.effects);
         generalize = (uu___99_13785.generalize);
         letrecs = (uu___99_13785.letrecs);
         top_level = (uu___99_13785.top_level);
         check_uvars = (uu___99_13785.check_uvars);
         use_eq = (uu___99_13785.use_eq);
         is_iface = (uu___99_13785.is_iface);
         admit = (uu___99_13785.admit);
         lax = (uu___99_13785.lax);
         lax_universes = (uu___99_13785.lax_universes);
         failhard = (uu___99_13785.failhard);
         nosynth = (uu___99_13785.nosynth);
         tc_term = (uu___99_13785.tc_term);
         type_of = (uu___99_13785.type_of);
         universe_of = (uu___99_13785.universe_of);
         use_bv_sorts = (uu___99_13785.use_bv_sorts);
         qname_and_index = (uu___99_13785.qname_and_index);
         proof_ns = (uu___99_13785.proof_ns);
         synth = (uu___99_13785.synth);
         is_native_tactic = (uu___99_13785.is_native_tactic);
         identifier_info = (uu___99_13785.identifier_info);
         tc_hooks = (uu___99_13785.tc_hooks);
         dsenv = (uu___99_13785.dsenv);
         dep_graph = (uu___99_13785.dep_graph)
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
      let uu___100_13816 = env  in
      {
        solver = (uu___100_13816.solver);
        range = (uu___100_13816.range);
        curmodule = (uu___100_13816.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___100_13816.gamma_cache);
        modules = (uu___100_13816.modules);
        expected_typ = (uu___100_13816.expected_typ);
        sigtab = (uu___100_13816.sigtab);
        is_pattern = (uu___100_13816.is_pattern);
        instantiate_imp = (uu___100_13816.instantiate_imp);
        effects = (uu___100_13816.effects);
        generalize = (uu___100_13816.generalize);
        letrecs = (uu___100_13816.letrecs);
        top_level = (uu___100_13816.top_level);
        check_uvars = (uu___100_13816.check_uvars);
        use_eq = (uu___100_13816.use_eq);
        is_iface = (uu___100_13816.is_iface);
        admit = (uu___100_13816.admit);
        lax = (uu___100_13816.lax);
        lax_universes = (uu___100_13816.lax_universes);
        failhard = (uu___100_13816.failhard);
        nosynth = (uu___100_13816.nosynth);
        tc_term = (uu___100_13816.tc_term);
        type_of = (uu___100_13816.type_of);
        universe_of = (uu___100_13816.universe_of);
        use_bv_sorts = (uu___100_13816.use_bv_sorts);
        qname_and_index = (uu___100_13816.qname_and_index);
        proof_ns = (uu___100_13816.proof_ns);
        synth = (uu___100_13816.synth);
        is_native_tactic = (uu___100_13816.is_native_tactic);
        identifier_info = (uu___100_13816.identifier_info);
        tc_hooks = (uu___100_13816.tc_hooks);
        dsenv = (uu___100_13816.dsenv);
        dep_graph = (uu___100_13816.dep_graph)
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
            (let uu___101_13847 = env  in
             {
               solver = (uu___101_13847.solver);
               range = (uu___101_13847.range);
               curmodule = (uu___101_13847.curmodule);
               gamma = rest;
               gamma_cache = (uu___101_13847.gamma_cache);
               modules = (uu___101_13847.modules);
               expected_typ = (uu___101_13847.expected_typ);
               sigtab = (uu___101_13847.sigtab);
               is_pattern = (uu___101_13847.is_pattern);
               instantiate_imp = (uu___101_13847.instantiate_imp);
               effects = (uu___101_13847.effects);
               generalize = (uu___101_13847.generalize);
               letrecs = (uu___101_13847.letrecs);
               top_level = (uu___101_13847.top_level);
               check_uvars = (uu___101_13847.check_uvars);
               use_eq = (uu___101_13847.use_eq);
               is_iface = (uu___101_13847.is_iface);
               admit = (uu___101_13847.admit);
               lax = (uu___101_13847.lax);
               lax_universes = (uu___101_13847.lax_universes);
               failhard = (uu___101_13847.failhard);
               nosynth = (uu___101_13847.nosynth);
               tc_term = (uu___101_13847.tc_term);
               type_of = (uu___101_13847.type_of);
               universe_of = (uu___101_13847.universe_of);
               use_bv_sorts = (uu___101_13847.use_bv_sorts);
               qname_and_index = (uu___101_13847.qname_and_index);
               proof_ns = (uu___101_13847.proof_ns);
               synth = (uu___101_13847.synth);
               is_native_tactic = (uu___101_13847.is_native_tactic);
               identifier_info = (uu___101_13847.identifier_info);
               tc_hooks = (uu___101_13847.tc_hooks);
               dsenv = (uu___101_13847.dsenv);
               dep_graph = (uu___101_13847.dep_graph)
             }))
    | uu____13848 -> FStar_Pervasives_Native.None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13870  ->
             match uu____13870 with | (x,uu____13876) -> push_bv env1 x) env
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
            let uu___102_13904 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___102_13904.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___102_13904.FStar_Syntax_Syntax.index);
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
      (let uu___103_13934 = env  in
       {
         solver = (uu___103_13934.solver);
         range = (uu___103_13934.range);
         curmodule = (uu___103_13934.curmodule);
         gamma = [];
         gamma_cache = (uu___103_13934.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___103_13934.sigtab);
         is_pattern = (uu___103_13934.is_pattern);
         instantiate_imp = (uu___103_13934.instantiate_imp);
         effects = (uu___103_13934.effects);
         generalize = (uu___103_13934.generalize);
         letrecs = (uu___103_13934.letrecs);
         top_level = (uu___103_13934.top_level);
         check_uvars = (uu___103_13934.check_uvars);
         use_eq = (uu___103_13934.use_eq);
         is_iface = (uu___103_13934.is_iface);
         admit = (uu___103_13934.admit);
         lax = (uu___103_13934.lax);
         lax_universes = (uu___103_13934.lax_universes);
         failhard = (uu___103_13934.failhard);
         nosynth = (uu___103_13934.nosynth);
         tc_term = (uu___103_13934.tc_term);
         type_of = (uu___103_13934.type_of);
         universe_of = (uu___103_13934.universe_of);
         use_bv_sorts = (uu___103_13934.use_bv_sorts);
         qname_and_index = (uu___103_13934.qname_and_index);
         proof_ns = (uu___103_13934.proof_ns);
         synth = (uu___103_13934.synth);
         is_native_tactic = (uu___103_13934.is_native_tactic);
         identifier_info = (uu___103_13934.identifier_info);
         tc_hooks = (uu___103_13934.tc_hooks);
         dsenv = (uu___103_13934.dsenv);
         dep_graph = (uu___103_13934.dep_graph)
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
        let uu____13966 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____13966 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____13994 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____13994)
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___104_14007 = env  in
      {
        solver = (uu___104_14007.solver);
        range = (uu___104_14007.range);
        curmodule = (uu___104_14007.curmodule);
        gamma = (uu___104_14007.gamma);
        gamma_cache = (uu___104_14007.gamma_cache);
        modules = (uu___104_14007.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___104_14007.sigtab);
        is_pattern = (uu___104_14007.is_pattern);
        instantiate_imp = (uu___104_14007.instantiate_imp);
        effects = (uu___104_14007.effects);
        generalize = (uu___104_14007.generalize);
        letrecs = (uu___104_14007.letrecs);
        top_level = (uu___104_14007.top_level);
        check_uvars = (uu___104_14007.check_uvars);
        use_eq = false;
        is_iface = (uu___104_14007.is_iface);
        admit = (uu___104_14007.admit);
        lax = (uu___104_14007.lax);
        lax_universes = (uu___104_14007.lax_universes);
        failhard = (uu___104_14007.failhard);
        nosynth = (uu___104_14007.nosynth);
        tc_term = (uu___104_14007.tc_term);
        type_of = (uu___104_14007.type_of);
        universe_of = (uu___104_14007.universe_of);
        use_bv_sorts = (uu___104_14007.use_bv_sorts);
        qname_and_index = (uu___104_14007.qname_and_index);
        proof_ns = (uu___104_14007.proof_ns);
        synth = (uu___104_14007.synth);
        is_native_tactic = (uu___104_14007.is_native_tactic);
        identifier_info = (uu___104_14007.identifier_info);
        tc_hooks = (uu___104_14007.tc_hooks);
        dsenv = (uu___104_14007.dsenv);
        dep_graph = (uu___104_14007.dep_graph)
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
    let uu____14031 = expected_typ env_  in
    ((let uu___105_14037 = env_  in
      {
        solver = (uu___105_14037.solver);
        range = (uu___105_14037.range);
        curmodule = (uu___105_14037.curmodule);
        gamma = (uu___105_14037.gamma);
        gamma_cache = (uu___105_14037.gamma_cache);
        modules = (uu___105_14037.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___105_14037.sigtab);
        is_pattern = (uu___105_14037.is_pattern);
        instantiate_imp = (uu___105_14037.instantiate_imp);
        effects = (uu___105_14037.effects);
        generalize = (uu___105_14037.generalize);
        letrecs = (uu___105_14037.letrecs);
        top_level = (uu___105_14037.top_level);
        check_uvars = (uu___105_14037.check_uvars);
        use_eq = false;
        is_iface = (uu___105_14037.is_iface);
        admit = (uu___105_14037.admit);
        lax = (uu___105_14037.lax);
        lax_universes = (uu___105_14037.lax_universes);
        failhard = (uu___105_14037.failhard);
        nosynth = (uu___105_14037.nosynth);
        tc_term = (uu___105_14037.tc_term);
        type_of = (uu___105_14037.type_of);
        universe_of = (uu___105_14037.universe_of);
        use_bv_sorts = (uu___105_14037.use_bv_sorts);
        qname_and_index = (uu___105_14037.qname_and_index);
        proof_ns = (uu___105_14037.proof_ns);
        synth = (uu___105_14037.synth);
        is_native_tactic = (uu___105_14037.is_native_tactic);
        identifier_info = (uu___105_14037.identifier_info);
        tc_hooks = (uu___105_14037.tc_hooks);
        dsenv = (uu___105_14037.dsenv);
        dep_graph = (uu___105_14037.dep_graph)
      }), uu____14031)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____14050 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___79_14060  ->
                    match uu___79_14060 with
                    | Binding_sig (uu____14063,se) -> [se]
                    | uu____14069 -> []))
             in
          FStar_All.pipe_right uu____14050 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___106_14076 = env  in
       {
         solver = (uu___106_14076.solver);
         range = (uu___106_14076.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___106_14076.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___106_14076.expected_typ);
         sigtab = (uu___106_14076.sigtab);
         is_pattern = (uu___106_14076.is_pattern);
         instantiate_imp = (uu___106_14076.instantiate_imp);
         effects = (uu___106_14076.effects);
         generalize = (uu___106_14076.generalize);
         letrecs = (uu___106_14076.letrecs);
         top_level = (uu___106_14076.top_level);
         check_uvars = (uu___106_14076.check_uvars);
         use_eq = (uu___106_14076.use_eq);
         is_iface = (uu___106_14076.is_iface);
         admit = (uu___106_14076.admit);
         lax = (uu___106_14076.lax);
         lax_universes = (uu___106_14076.lax_universes);
         failhard = (uu___106_14076.failhard);
         nosynth = (uu___106_14076.nosynth);
         tc_term = (uu___106_14076.tc_term);
         type_of = (uu___106_14076.type_of);
         universe_of = (uu___106_14076.universe_of);
         use_bv_sorts = (uu___106_14076.use_bv_sorts);
         qname_and_index = (uu___106_14076.qname_and_index);
         proof_ns = (uu___106_14076.proof_ns);
         synth = (uu___106_14076.synth);
         is_native_tactic = (uu___106_14076.is_native_tactic);
         identifier_info = (uu___106_14076.identifier_info);
         tc_hooks = (uu___106_14076.tc_hooks);
         dsenv = (uu___106_14076.dsenv);
         dep_graph = (uu___106_14076.dep_graph)
       })
  
let uvars_in_env : env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14157)::tl1 -> aux out tl1
      | (Binding_lid (uu____14161,(uu____14162,t)))::tl1 ->
          let uu____14177 =
            let uu____14184 = FStar_Syntax_Free.uvars t  in
            ext out uu____14184  in
          aux uu____14177 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14191;
            FStar_Syntax_Syntax.index = uu____14192;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14199 =
            let uu____14206 = FStar_Syntax_Free.uvars t  in
            ext out uu____14206  in
          aux uu____14199 tl1
      | (Binding_sig uu____14213)::uu____14214 -> out
      | (Binding_sig_inst uu____14223)::uu____14224 -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14279)::tl1 -> aux out tl1
      | (Binding_univ uu____14291)::tl1 -> aux out tl1
      | (Binding_lid (uu____14295,(uu____14296,t)))::tl1 ->
          let uu____14311 =
            let uu____14314 = FStar_Syntax_Free.univs t  in
            ext out uu____14314  in
          aux uu____14311 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14317;
            FStar_Syntax_Syntax.index = uu____14318;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14325 =
            let uu____14328 = FStar_Syntax_Free.univs t  in
            ext out uu____14328  in
          aux uu____14325 tl1
      | (Binding_sig uu____14331)::uu____14332 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14385)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14401 = FStar_Util.fifo_set_add uname out  in
          aux uu____14401 tl1
      | (Binding_lid (uu____14404,(uu____14405,t)))::tl1 ->
          let uu____14420 =
            let uu____14423 = FStar_Syntax_Free.univnames t  in
            ext out uu____14423  in
          aux uu____14420 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14426;
            FStar_Syntax_Syntax.index = uu____14427;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14434 =
            let uu____14437 = FStar_Syntax_Free.univnames t  in
            ext out uu____14437  in
          aux uu____14434 tl1
      | (Binding_sig uu____14440)::uu____14441 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___80_14465  ->
            match uu___80_14465 with
            | Binding_var x -> [x]
            | Binding_lid uu____14469 -> []
            | Binding_sig uu____14474 -> []
            | Binding_univ uu____14481 -> []
            | Binding_sig_inst uu____14482 -> []))
  
let binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14498 =
      let uu____14501 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14501
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14498 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____14523 =
      let uu____14524 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___81_14534  ->
                match uu___81_14534 with
                | Binding_var x ->
                    let uu____14536 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14536
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14539) ->
                    let uu____14540 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14540
                | Binding_sig (ls,uu____14542) ->
                    let uu____14547 =
                      let uu____14548 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14548
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14547
                | Binding_sig_inst (ls,uu____14558,uu____14559) ->
                    let uu____14564 =
                      let uu____14565 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14565
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14564))
         in
      FStar_All.pipe_right uu____14524 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14523 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14582 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14582
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14610  ->
                 fun uu____14611  ->
                   match (uu____14610, uu____14611) with
                   | ((b1,uu____14629),(b2,uu____14631)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let string_of_delta_level : delta_level -> Prims.string =
  fun uu___82_14673  ->
    match uu___82_14673 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14674 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___83_14692  ->
             match uu___83_14692 with
             | Binding_sig (lids,uu____14698) -> FStar_List.append lids keys
             | uu____14703 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14709  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let should_enc_path : env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14743) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14762,uu____14763) -> false  in
      let uu____14772 =
        FStar_List.tryFind
          (fun uu____14790  ->
             match uu____14790 with | (p,uu____14798) -> list_prefix p path)
          env.proof_ns
         in
      match uu____14772 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14809,b) -> b
  
let should_enc_lid : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14827 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____14827
  
let cons_proof_ns : Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___107_14839 = e  in
        {
          solver = (uu___107_14839.solver);
          range = (uu___107_14839.range);
          curmodule = (uu___107_14839.curmodule);
          gamma = (uu___107_14839.gamma);
          gamma_cache = (uu___107_14839.gamma_cache);
          modules = (uu___107_14839.modules);
          expected_typ = (uu___107_14839.expected_typ);
          sigtab = (uu___107_14839.sigtab);
          is_pattern = (uu___107_14839.is_pattern);
          instantiate_imp = (uu___107_14839.instantiate_imp);
          effects = (uu___107_14839.effects);
          generalize = (uu___107_14839.generalize);
          letrecs = (uu___107_14839.letrecs);
          top_level = (uu___107_14839.top_level);
          check_uvars = (uu___107_14839.check_uvars);
          use_eq = (uu___107_14839.use_eq);
          is_iface = (uu___107_14839.is_iface);
          admit = (uu___107_14839.admit);
          lax = (uu___107_14839.lax);
          lax_universes = (uu___107_14839.lax_universes);
          failhard = (uu___107_14839.failhard);
          nosynth = (uu___107_14839.nosynth);
          tc_term = (uu___107_14839.tc_term);
          type_of = (uu___107_14839.type_of);
          universe_of = (uu___107_14839.universe_of);
          use_bv_sorts = (uu___107_14839.use_bv_sorts);
          qname_and_index = (uu___107_14839.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___107_14839.synth);
          is_native_tactic = (uu___107_14839.is_native_tactic);
          identifier_info = (uu___107_14839.identifier_info);
          tc_hooks = (uu___107_14839.tc_hooks);
          dsenv = (uu___107_14839.dsenv);
          dep_graph = (uu___107_14839.dep_graph)
        }
  
let add_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path 
let rem_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path 
let get_proof_ns : env -> proof_namespace = fun e  -> e.proof_ns 
let set_proof_ns : proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___108_14865 = e  in
      {
        solver = (uu___108_14865.solver);
        range = (uu___108_14865.range);
        curmodule = (uu___108_14865.curmodule);
        gamma = (uu___108_14865.gamma);
        gamma_cache = (uu___108_14865.gamma_cache);
        modules = (uu___108_14865.modules);
        expected_typ = (uu___108_14865.expected_typ);
        sigtab = (uu___108_14865.sigtab);
        is_pattern = (uu___108_14865.is_pattern);
        instantiate_imp = (uu___108_14865.instantiate_imp);
        effects = (uu___108_14865.effects);
        generalize = (uu___108_14865.generalize);
        letrecs = (uu___108_14865.letrecs);
        top_level = (uu___108_14865.top_level);
        check_uvars = (uu___108_14865.check_uvars);
        use_eq = (uu___108_14865.use_eq);
        is_iface = (uu___108_14865.is_iface);
        admit = (uu___108_14865.admit);
        lax = (uu___108_14865.lax);
        lax_universes = (uu___108_14865.lax_universes);
        failhard = (uu___108_14865.failhard);
        nosynth = (uu___108_14865.nosynth);
        tc_term = (uu___108_14865.tc_term);
        type_of = (uu___108_14865.type_of);
        universe_of = (uu___108_14865.universe_of);
        use_bv_sorts = (uu___108_14865.use_bv_sorts);
        qname_and_index = (uu___108_14865.qname_and_index);
        proof_ns = ns;
        synth = (uu___108_14865.synth);
        is_native_tactic = (uu___108_14865.is_native_tactic);
        identifier_info = (uu___108_14865.identifier_info);
        tc_hooks = (uu___108_14865.tc_hooks);
        dsenv = (uu___108_14865.dsenv);
        dep_graph = (uu___108_14865.dep_graph)
      }
  
let unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14876 = FStar_Syntax_Free.names t  in
      let uu____14879 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14876 uu____14879
  
let closed : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14896 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____14896
  
let closed' : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14902 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____14902
  
let string_of_proof_ns : env -> Prims.string =
  fun env  ->
    let aux uu____14917 =
      match uu____14917 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14933 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____14933)
       in
    let uu____14935 =
      let uu____14938 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____14938 FStar_List.rev  in
    FStar_All.pipe_right uu____14935 (FStar_String.concat " ")
  
let dummy_solver : solver_t =
  {
    init = (fun uu____14955  -> ());
    push = (fun uu____14957  -> ());
    pop = (fun uu____14959  -> ());
    encode_modul = (fun uu____14962  -> fun uu____14963  -> ());
    encode_sig = (fun uu____14966  -> fun uu____14967  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14973 =
             let uu____14980 = FStar_Options.peek ()  in (e, g, uu____14980)
              in
           [uu____14973]);
    solve = (fun uu____14996  -> fun uu____14997  -> fun uu____14998  -> ());
    finish = (fun uu____15004  -> ());
    refresh = (fun uu____15006  -> ())
  } 