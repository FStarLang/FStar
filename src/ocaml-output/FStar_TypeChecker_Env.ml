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
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
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
  dsenv: FStar_Syntax_DsEnv.env ;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qtbl_name_and_index
  
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
        qtbl_name_and_index = __fname__qtbl_name_and_index;
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
           (fun uu___71_5753  ->
              match uu___71_5753 with
              | Binding_var x ->
                  let y =
                    let uu____5756 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____5756  in
                  let uu____5757 =
                    let uu____5758 = FStar_Syntax_Subst.compress y  in
                    uu____5758.FStar_Syntax_Syntax.n  in
                  (match uu____5757 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5762 =
                         let uu___86_5763 = y1  in
                         let uu____5764 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___86_5763.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___86_5763.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5764
                         }  in
                       Binding_var uu____5762
                   | uu____5767 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___87_5775 = env  in
      let uu____5776 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___87_5775.solver);
        range = (uu___87_5775.range);
        curmodule = (uu___87_5775.curmodule);
        gamma = uu____5776;
        gamma_cache = (uu___87_5775.gamma_cache);
        modules = (uu___87_5775.modules);
        expected_typ = (uu___87_5775.expected_typ);
        sigtab = (uu___87_5775.sigtab);
        is_pattern = (uu___87_5775.is_pattern);
        instantiate_imp = (uu___87_5775.instantiate_imp);
        effects = (uu___87_5775.effects);
        generalize = (uu___87_5775.generalize);
        letrecs = (uu___87_5775.letrecs);
        top_level = (uu___87_5775.top_level);
        check_uvars = (uu___87_5775.check_uvars);
        use_eq = (uu___87_5775.use_eq);
        is_iface = (uu___87_5775.is_iface);
        admit = (uu___87_5775.admit);
        lax = (uu___87_5775.lax);
        lax_universes = (uu___87_5775.lax_universes);
        failhard = (uu___87_5775.failhard);
        nosynth = (uu___87_5775.nosynth);
        tc_term = (uu___87_5775.tc_term);
        type_of = (uu___87_5775.type_of);
        universe_of = (uu___87_5775.universe_of);
        check_type_of = (uu___87_5775.check_type_of);
        use_bv_sorts = (uu___87_5775.use_bv_sorts);
        qtbl_name_and_index = (uu___87_5775.qtbl_name_and_index);
        proof_ns = (uu___87_5775.proof_ns);
        synth = (uu___87_5775.synth);
        is_native_tactic = (uu___87_5775.is_native_tactic);
        identifier_info = (uu___87_5775.identifier_info);
        tc_hooks = (uu___87_5775.tc_hooks);
        dsenv = (uu___87_5775.dsenv);
        dep_graph = (uu___87_5775.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____5783  -> fun uu____5784  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___88_5794 = env  in
      {
        solver = (uu___88_5794.solver);
        range = (uu___88_5794.range);
        curmodule = (uu___88_5794.curmodule);
        gamma = (uu___88_5794.gamma);
        gamma_cache = (uu___88_5794.gamma_cache);
        modules = (uu___88_5794.modules);
        expected_typ = (uu___88_5794.expected_typ);
        sigtab = (uu___88_5794.sigtab);
        is_pattern = (uu___88_5794.is_pattern);
        instantiate_imp = (uu___88_5794.instantiate_imp);
        effects = (uu___88_5794.effects);
        generalize = (uu___88_5794.generalize);
        letrecs = (uu___88_5794.letrecs);
        top_level = (uu___88_5794.top_level);
        check_uvars = (uu___88_5794.check_uvars);
        use_eq = (uu___88_5794.use_eq);
        is_iface = (uu___88_5794.is_iface);
        admit = (uu___88_5794.admit);
        lax = (uu___88_5794.lax);
        lax_universes = (uu___88_5794.lax_universes);
        failhard = (uu___88_5794.failhard);
        nosynth = (uu___88_5794.nosynth);
        tc_term = (uu___88_5794.tc_term);
        type_of = (uu___88_5794.type_of);
        universe_of = (uu___88_5794.universe_of);
        check_type_of = (uu___88_5794.check_type_of);
        use_bv_sorts = (uu___88_5794.use_bv_sorts);
        qtbl_name_and_index = (uu___88_5794.qtbl_name_and_index);
        proof_ns = (uu___88_5794.proof_ns);
        synth = (uu___88_5794.synth);
        is_native_tactic = (uu___88_5794.is_native_tactic);
        identifier_info = (uu___88_5794.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___88_5794.dsenv);
        dep_graph = (uu___88_5794.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___89_5801 = e  in
      {
        solver = (uu___89_5801.solver);
        range = (uu___89_5801.range);
        curmodule = (uu___89_5801.curmodule);
        gamma = (uu___89_5801.gamma);
        gamma_cache = (uu___89_5801.gamma_cache);
        modules = (uu___89_5801.modules);
        expected_typ = (uu___89_5801.expected_typ);
        sigtab = (uu___89_5801.sigtab);
        is_pattern = (uu___89_5801.is_pattern);
        instantiate_imp = (uu___89_5801.instantiate_imp);
        effects = (uu___89_5801.effects);
        generalize = (uu___89_5801.generalize);
        letrecs = (uu___89_5801.letrecs);
        top_level = (uu___89_5801.top_level);
        check_uvars = (uu___89_5801.check_uvars);
        use_eq = (uu___89_5801.use_eq);
        is_iface = (uu___89_5801.is_iface);
        admit = (uu___89_5801.admit);
        lax = (uu___89_5801.lax);
        lax_universes = (uu___89_5801.lax_universes);
        failhard = (uu___89_5801.failhard);
        nosynth = (uu___89_5801.nosynth);
        tc_term = (uu___89_5801.tc_term);
        type_of = (uu___89_5801.type_of);
        universe_of = (uu___89_5801.universe_of);
        check_type_of = (uu___89_5801.check_type_of);
        use_bv_sorts = (uu___89_5801.use_bv_sorts);
        qtbl_name_and_index = (uu___89_5801.qtbl_name_and_index);
        proof_ns = (uu___89_5801.proof_ns);
        synth = (uu___89_5801.synth);
        is_native_tactic = (uu___89_5801.is_native_tactic);
        identifier_info = (uu___89_5801.identifier_info);
        tc_hooks = (uu___89_5801.tc_hooks);
        dsenv = (uu___89_5801.dsenv);
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
      | (NoDelta ,uu____5816) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5817,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5818,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5819 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____5826 . Prims.unit -> 'Auu____5826 FStar_Util.smap =
  fun uu____5832  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____5835 . Prims.unit -> 'Auu____5835 FStar_Util.smap =
  fun uu____5841  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____5937 = new_gamma_cache ()  in
                let uu____5940 = new_sigtab ()  in
                let uu____5943 =
                  let uu____5956 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____5956, FStar_Pervasives_Native.None)  in
                let uu____5971 = FStar_Options.using_facts_from ()  in
                let uu____5972 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____5975 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____5937;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____5940;
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
                  qtbl_name_and_index = uu____5943;
                  proof_ns = uu____5971;
                  synth =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  is_native_tactic = (fun uu____6005  -> false);
                  identifier_info = uu____5972;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____5975;
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
let (push_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6088  ->
    let uu____6089 = FStar_ST.op_Bang query_indices  in
    match uu____6089 with
    | [] -> failwith "Empty query indices!"
    | uu____6139 ->
        let uu____6148 =
          let uu____6157 =
            let uu____6164 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____6164  in
          let uu____6214 = FStar_ST.op_Bang query_indices  in uu____6157 ::
            uu____6214
           in
        FStar_ST.op_Colon_Equals query_indices uu____6148
  
let (pop_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6301  ->
    let uu____6302 = FStar_ST.op_Bang query_indices  in
    match uu____6302 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____6415  ->
    match uu____6415 with
    | (l,n1) ->
        let uu____6422 = FStar_ST.op_Bang query_indices  in
        (match uu____6422 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6533 -> failwith "Empty query indices")
  
let (peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6550  ->
    let uu____6551 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6551
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____6622 =
       let uu____6625 = FStar_ST.op_Bang stack  in env :: uu____6625  in
     FStar_ST.op_Colon_Equals stack uu____6622);
    (let uu___90_6674 = env  in
     let uu____6675 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6678 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6681 =
       let uu____6694 =
         let uu____6697 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____6697  in
       let uu____6722 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____6694, uu____6722)  in
     let uu____6763 =
       let uu____6766 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6766  in
     {
       solver = (uu___90_6674.solver);
       range = (uu___90_6674.range);
       curmodule = (uu___90_6674.curmodule);
       gamma = (uu___90_6674.gamma);
       gamma_cache = uu____6675;
       modules = (uu___90_6674.modules);
       expected_typ = (uu___90_6674.expected_typ);
       sigtab = uu____6678;
       is_pattern = (uu___90_6674.is_pattern);
       instantiate_imp = (uu___90_6674.instantiate_imp);
       effects = (uu___90_6674.effects);
       generalize = (uu___90_6674.generalize);
       letrecs = (uu___90_6674.letrecs);
       top_level = (uu___90_6674.top_level);
       check_uvars = (uu___90_6674.check_uvars);
       use_eq = (uu___90_6674.use_eq);
       is_iface = (uu___90_6674.is_iface);
       admit = (uu___90_6674.admit);
       lax = (uu___90_6674.lax);
       lax_universes = (uu___90_6674.lax_universes);
       failhard = (uu___90_6674.failhard);
       nosynth = (uu___90_6674.nosynth);
       tc_term = (uu___90_6674.tc_term);
       type_of = (uu___90_6674.type_of);
       universe_of = (uu___90_6674.universe_of);
       check_type_of = (uu___90_6674.check_type_of);
       use_bv_sorts = (uu___90_6674.use_bv_sorts);
       qtbl_name_and_index = uu____6681;
       proof_ns = (uu___90_6674.proof_ns);
       synth = (uu___90_6674.synth);
       is_native_tactic = (uu___90_6674.is_native_tactic);
       identifier_info = uu____6763;
       tc_hooks = (uu___90_6674.tc_hooks);
       dsenv = (uu___90_6674.dsenv);
       dep_graph = (uu___90_6674.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____6810  ->
    let uu____6811 = FStar_ST.op_Bang stack  in
    match uu____6811 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6865 -> failwith "Impossible: Too many pops"
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____6894,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____6926 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6952  ->
                  match uu____6952 with
                  | (m,uu____6958) -> FStar_Ident.lid_equals l m))
           in
        (match uu____6926 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___91_6966 = env  in
               {
                 solver = (uu___91_6966.solver);
                 range = (uu___91_6966.range);
                 curmodule = (uu___91_6966.curmodule);
                 gamma = (uu___91_6966.gamma);
                 gamma_cache = (uu___91_6966.gamma_cache);
                 modules = (uu___91_6966.modules);
                 expected_typ = (uu___91_6966.expected_typ);
                 sigtab = (uu___91_6966.sigtab);
                 is_pattern = (uu___91_6966.is_pattern);
                 instantiate_imp = (uu___91_6966.instantiate_imp);
                 effects = (uu___91_6966.effects);
                 generalize = (uu___91_6966.generalize);
                 letrecs = (uu___91_6966.letrecs);
                 top_level = (uu___91_6966.top_level);
                 check_uvars = (uu___91_6966.check_uvars);
                 use_eq = (uu___91_6966.use_eq);
                 is_iface = (uu___91_6966.is_iface);
                 admit = (uu___91_6966.admit);
                 lax = (uu___91_6966.lax);
                 lax_universes = (uu___91_6966.lax_universes);
                 failhard = (uu___91_6966.failhard);
                 nosynth = (uu___91_6966.nosynth);
                 tc_term = (uu___91_6966.tc_term);
                 type_of = (uu___91_6966.type_of);
                 universe_of = (uu___91_6966.universe_of);
                 check_type_of = (uu___91_6966.check_type_of);
                 use_bv_sorts = (uu___91_6966.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___91_6966.proof_ns);
                 synth = (uu___91_6966.synth);
                 is_native_tactic = (uu___91_6966.is_native_tactic);
                 identifier_info = (uu___91_6966.identifier_info);
                 tc_hooks = (uu___91_6966.tc_hooks);
                 dsenv = (uu___91_6966.dsenv);
                 dep_graph = (uu___91_6966.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6979,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___92_6988 = env  in
               {
                 solver = (uu___92_6988.solver);
                 range = (uu___92_6988.range);
                 curmodule = (uu___92_6988.curmodule);
                 gamma = (uu___92_6988.gamma);
                 gamma_cache = (uu___92_6988.gamma_cache);
                 modules = (uu___92_6988.modules);
                 expected_typ = (uu___92_6988.expected_typ);
                 sigtab = (uu___92_6988.sigtab);
                 is_pattern = (uu___92_6988.is_pattern);
                 instantiate_imp = (uu___92_6988.instantiate_imp);
                 effects = (uu___92_6988.effects);
                 generalize = (uu___92_6988.generalize);
                 letrecs = (uu___92_6988.letrecs);
                 top_level = (uu___92_6988.top_level);
                 check_uvars = (uu___92_6988.check_uvars);
                 use_eq = (uu___92_6988.use_eq);
                 is_iface = (uu___92_6988.is_iface);
                 admit = (uu___92_6988.admit);
                 lax = (uu___92_6988.lax);
                 lax_universes = (uu___92_6988.lax_universes);
                 failhard = (uu___92_6988.failhard);
                 nosynth = (uu___92_6988.nosynth);
                 tc_term = (uu___92_6988.tc_term);
                 type_of = (uu___92_6988.type_of);
                 universe_of = (uu___92_6988.universe_of);
                 check_type_of = (uu___92_6988.check_type_of);
                 use_bv_sorts = (uu___92_6988.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___92_6988.proof_ns);
                 synth = (uu___92_6988.synth);
                 is_native_tactic = (uu___92_6988.is_native_tactic);
                 identifier_info = (uu___92_6988.identifier_info);
                 tc_hooks = (uu___92_6988.tc_hooks);
                 dsenv = (uu___92_6988.dsenv);
                 dep_graph = (uu___92_6988.dep_graph)
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
        (let uu___93_7014 = e  in
         {
           solver = (uu___93_7014.solver);
           range = r;
           curmodule = (uu___93_7014.curmodule);
           gamma = (uu___93_7014.gamma);
           gamma_cache = (uu___93_7014.gamma_cache);
           modules = (uu___93_7014.modules);
           expected_typ = (uu___93_7014.expected_typ);
           sigtab = (uu___93_7014.sigtab);
           is_pattern = (uu___93_7014.is_pattern);
           instantiate_imp = (uu___93_7014.instantiate_imp);
           effects = (uu___93_7014.effects);
           generalize = (uu___93_7014.generalize);
           letrecs = (uu___93_7014.letrecs);
           top_level = (uu___93_7014.top_level);
           check_uvars = (uu___93_7014.check_uvars);
           use_eq = (uu___93_7014.use_eq);
           is_iface = (uu___93_7014.is_iface);
           admit = (uu___93_7014.admit);
           lax = (uu___93_7014.lax);
           lax_universes = (uu___93_7014.lax_universes);
           failhard = (uu___93_7014.failhard);
           nosynth = (uu___93_7014.nosynth);
           tc_term = (uu___93_7014.tc_term);
           type_of = (uu___93_7014.type_of);
           universe_of = (uu___93_7014.universe_of);
           check_type_of = (uu___93_7014.check_type_of);
           use_bv_sorts = (uu___93_7014.use_bv_sorts);
           qtbl_name_and_index = (uu___93_7014.qtbl_name_and_index);
           proof_ns = (uu___93_7014.proof_ns);
           synth = (uu___93_7014.synth);
           is_native_tactic = (uu___93_7014.is_native_tactic);
           identifier_info = (uu___93_7014.identifier_info);
           tc_hooks = (uu___93_7014.tc_hooks);
           dsenv = (uu___93_7014.dsenv);
           dep_graph = (uu___93_7014.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____7024 =
        let uu____7025 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____7025 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7024
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____7073 =
          let uu____7074 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____7074 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7073
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____7122 =
          let uu____7123 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____7123 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7122
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____7173 =
        let uu____7174 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____7174 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7173
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___94_7227 = env  in
      {
        solver = (uu___94_7227.solver);
        range = (uu___94_7227.range);
        curmodule = lid;
        gamma = (uu___94_7227.gamma);
        gamma_cache = (uu___94_7227.gamma_cache);
        modules = (uu___94_7227.modules);
        expected_typ = (uu___94_7227.expected_typ);
        sigtab = (uu___94_7227.sigtab);
        is_pattern = (uu___94_7227.is_pattern);
        instantiate_imp = (uu___94_7227.instantiate_imp);
        effects = (uu___94_7227.effects);
        generalize = (uu___94_7227.generalize);
        letrecs = (uu___94_7227.letrecs);
        top_level = (uu___94_7227.top_level);
        check_uvars = (uu___94_7227.check_uvars);
        use_eq = (uu___94_7227.use_eq);
        is_iface = (uu___94_7227.is_iface);
        admit = (uu___94_7227.admit);
        lax = (uu___94_7227.lax);
        lax_universes = (uu___94_7227.lax_universes);
        failhard = (uu___94_7227.failhard);
        nosynth = (uu___94_7227.nosynth);
        tc_term = (uu___94_7227.tc_term);
        type_of = (uu___94_7227.type_of);
        universe_of = (uu___94_7227.universe_of);
        check_type_of = (uu___94_7227.check_type_of);
        use_bv_sorts = (uu___94_7227.use_bv_sorts);
        qtbl_name_and_index = (uu___94_7227.qtbl_name_and_index);
        proof_ns = (uu___94_7227.proof_ns);
        synth = (uu___94_7227.synth);
        is_native_tactic = (uu___94_7227.is_native_tactic);
        identifier_info = (uu___94_7227.identifier_info);
        tc_hooks = (uu___94_7227.tc_hooks);
        dsenv = (uu___94_7227.dsenv);
        dep_graph = (uu___94_7227.dep_graph)
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
    let uu____7253 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7253)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____7261 =
      let uu____7262 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7262  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7261)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____7265  ->
    let uu____7266 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7266
  
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
      | ((formals,t),uu____7304) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7328 = FStar_Syntax_Subst.subst vs t  in (us, uu____7328)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___72_7341  ->
    match uu___72_7341 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7365  -> new_u_univ ()))
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
      let uu____7378 = inst_tscheme t  in
      match uu____7378 with
      | (us,t1) ->
          let uu____7389 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7389)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7401  ->
          match uu____7401 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7416 =
                         let uu____7417 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7418 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7419 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7420 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7417 uu____7418 uu____7419 uu____7420
                          in
                       failwith uu____7416)
                    else ();
                    (let uu____7422 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7422))
               | uu____7429 ->
                   let uu____7430 =
                     let uu____7431 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7431
                      in
                   failwith uu____7430)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____7435 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____7439 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7443 -> false
  
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
             | ([],uu____7477) -> Maybe
             | (uu____7484,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7503 -> No  in
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
          let uu____7588 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7588 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___73_7633  ->
                   match uu___73_7633 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7676 =
                           let uu____7695 =
                             let uu____7710 = inst_tscheme t  in
                             FStar_Util.Inl uu____7710  in
                           (uu____7695, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7676
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7776,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7778);
                                     FStar_Syntax_Syntax.sigrng = uu____7779;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7780;
                                     FStar_Syntax_Syntax.sigmeta = uu____7781;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7782;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7802 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7802
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7848 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7855 -> cache t  in
                       let uu____7856 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7856 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7931 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7931 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____8017 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____8077 = find_in_sigtab env lid  in
         match uu____8077 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8156) ->
          add_sigelts env ses
      | uu____8165 ->
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
            | uu____8179 -> ()))

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
        (fun uu___74_8206  ->
           match uu___74_8206 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8224 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____8277,lb::[]),uu____8279) ->
            let uu____8292 =
              let uu____8301 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____8310 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____8301, uu____8310)  in
            FStar_Pervasives_Native.Some uu____8292
        | FStar_Syntax_Syntax.Sig_let ((uu____8323,lbs),uu____8325) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____8361 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____8373 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____8373
                     then
                       let uu____8384 =
                         let uu____8393 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____8402 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____8393, uu____8402)  in
                       FStar_Pervasives_Native.Some uu____8384
                     else FStar_Pervasives_Native.None)
        | uu____8424 -> FStar_Pervasives_Native.None
  
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
          let uu____8477 =
            let uu____8486 =
              let uu____8491 =
                let uu____8492 =
                  let uu____8495 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____8495
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____8492)  in
              inst_tscheme1 uu____8491  in
            (uu____8486, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8477
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____8515,uu____8516) ->
          let uu____8521 =
            let uu____8530 =
              let uu____8535 =
                let uu____8536 =
                  let uu____8539 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____8539  in
                (us, uu____8536)  in
              inst_tscheme1 uu____8535  in
            (uu____8530, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8521
      | uu____8556 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____8634 =
          match uu____8634 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____8730,uvs,t,uu____8733,uu____8734,uu____8735);
                      FStar_Syntax_Syntax.sigrng = uu____8736;
                      FStar_Syntax_Syntax.sigquals = uu____8737;
                      FStar_Syntax_Syntax.sigmeta = uu____8738;
                      FStar_Syntax_Syntax.sigattrs = uu____8739;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8760 =
                     let uu____8769 = inst_tscheme1 (uvs, t)  in
                     (uu____8769, rng)  in
                   FStar_Pervasives_Native.Some uu____8760
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____8789;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____8791;
                      FStar_Syntax_Syntax.sigattrs = uu____8792;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8809 =
                     let uu____8810 = in_cur_mod env l  in uu____8810 = Yes
                      in
                   if uu____8809
                   then
                     let uu____8821 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____8821
                      then
                        let uu____8834 =
                          let uu____8843 = inst_tscheme1 (uvs, t)  in
                          (uu____8843, rng)  in
                        FStar_Pervasives_Native.Some uu____8834
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____8870 =
                        let uu____8879 = inst_tscheme1 (uvs, t)  in
                        (uu____8879, rng)  in
                      FStar_Pervasives_Native.Some uu____8870)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8900,uu____8901);
                      FStar_Syntax_Syntax.sigrng = uu____8902;
                      FStar_Syntax_Syntax.sigquals = uu____8903;
                      FStar_Syntax_Syntax.sigmeta = uu____8904;
                      FStar_Syntax_Syntax.sigattrs = uu____8905;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____8944 =
                          let uu____8953 = inst_tscheme1 (uvs, k)  in
                          (uu____8953, rng)  in
                        FStar_Pervasives_Native.Some uu____8944
                    | uu____8970 ->
                        let uu____8971 =
                          let uu____8980 =
                            let uu____8985 =
                              let uu____8986 =
                                let uu____8989 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8989
                                 in
                              (uvs, uu____8986)  in
                            inst_tscheme1 uu____8985  in
                          (uu____8980, rng)  in
                        FStar_Pervasives_Native.Some uu____8971)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9010,uu____9011);
                      FStar_Syntax_Syntax.sigrng = uu____9012;
                      FStar_Syntax_Syntax.sigquals = uu____9013;
                      FStar_Syntax_Syntax.sigmeta = uu____9014;
                      FStar_Syntax_Syntax.sigattrs = uu____9015;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____9055 =
                          let uu____9064 = inst_tscheme_with (uvs, k) us  in
                          (uu____9064, rng)  in
                        FStar_Pervasives_Native.Some uu____9055
                    | uu____9081 ->
                        let uu____9082 =
                          let uu____9091 =
                            let uu____9096 =
                              let uu____9097 =
                                let uu____9100 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9100
                                 in
                              (uvs, uu____9097)  in
                            inst_tscheme_with uu____9096 us  in
                          (uu____9091, rng)  in
                        FStar_Pervasives_Native.Some uu____9082)
               | FStar_Util.Inr se ->
                   let uu____9134 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____9155;
                          FStar_Syntax_Syntax.sigrng = uu____9156;
                          FStar_Syntax_Syntax.sigquals = uu____9157;
                          FStar_Syntax_Syntax.sigmeta = uu____9158;
                          FStar_Syntax_Syntax.sigattrs = uu____9159;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____9174 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____9134
                     (FStar_Util.map_option
                        (fun uu____9222  ->
                           match uu____9222 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____9253 =
          let uu____9264 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____9264 mapper  in
        match uu____9253 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            FStar_Pervasives_Native.Some
              ((us,
                 (let uu___95_9357 = t  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___95_9357.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                    FStar_Syntax_Syntax.vars =
                      (uu___95_9357.FStar_Syntax_Syntax.vars)
                  })), r)
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____9382 = lookup_qname env l  in
      match uu____9382 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9401 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9449 = try_lookup_bv env bv  in
      match uu____9449 with
      | FStar_Pervasives_Native.None  ->
          let uu____9464 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9464 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9479 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9480 =
            let uu____9481 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9481  in
          (uu____9479, uu____9480)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____9498 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____9498 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9564 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9564  in
          let uu____9565 =
            let uu____9574 =
              let uu____9579 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9579)  in
            (uu____9574, r1)  in
          FStar_Pervasives_Native.Some uu____9565
  
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
        let uu____9607 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____9607 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____9640,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____9665 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____9665  in
            let uu____9666 =
              let uu____9671 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____9671, r1)  in
            FStar_Pervasives_Native.Some uu____9666
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____9690 = try_lookup_lid env l  in
      match uu____9690 with
      | FStar_Pervasives_Native.None  ->
          let uu____9717 = name_not_found l  in
          FStar_Errors.raise_error uu____9717 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___75_9757  ->
              match uu___75_9757 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9759 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9774 = lookup_qname env lid  in
      match uu____9774 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9783,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9786;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9788;
              FStar_Syntax_Syntax.sigattrs = uu____9789;_},FStar_Pervasives_Native.None
            ),uu____9790)
          ->
          let uu____9839 =
            let uu____9850 =
              let uu____9855 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9855)  in
            (uu____9850, q)  in
          FStar_Pervasives_Native.Some uu____9839
      | uu____9872 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9889 = lookup_qname env lid  in
      match uu____9889 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9894,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9897;
              FStar_Syntax_Syntax.sigquals = uu____9898;
              FStar_Syntax_Syntax.sigmeta = uu____9899;
              FStar_Syntax_Syntax.sigattrs = uu____9900;_},FStar_Pervasives_Native.None
            ),uu____9901)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9950 ->
          let uu____9951 = name_not_found lid  in
          FStar_Errors.raise_error uu____9951 (FStar_Ident.range_of_lid lid)
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9970 = lookup_qname env lid  in
      match uu____9970 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9975,uvs,t,uu____9978,uu____9979,uu____9980);
              FStar_Syntax_Syntax.sigrng = uu____9981;
              FStar_Syntax_Syntax.sigquals = uu____9982;
              FStar_Syntax_Syntax.sigmeta = uu____9983;
              FStar_Syntax_Syntax.sigattrs = uu____9984;_},FStar_Pervasives_Native.None
            ),uu____9985)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____10038 ->
          let uu____10039 = name_not_found lid  in
          FStar_Errors.raise_error uu____10039 (FStar_Ident.range_of_lid lid)
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10060 = lookup_qname env lid  in
      match uu____10060 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10067,uu____10068,uu____10069,uu____10070,uu____10071,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10073;
              FStar_Syntax_Syntax.sigquals = uu____10074;
              FStar_Syntax_Syntax.sigmeta = uu____10075;
              FStar_Syntax_Syntax.sigattrs = uu____10076;_},uu____10077),uu____10078)
          -> (true, dcs)
      | uu____10139 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____10148 = lookup_qname env lid  in
      match uu____10148 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10149,uu____10150,uu____10151,l,uu____10153,uu____10154);
              FStar_Syntax_Syntax.sigrng = uu____10155;
              FStar_Syntax_Syntax.sigquals = uu____10156;
              FStar_Syntax_Syntax.sigmeta = uu____10157;
              FStar_Syntax_Syntax.sigattrs = uu____10158;_},uu____10159),uu____10160)
          -> l
      | uu____10215 ->
          let uu____10216 =
            let uu____10217 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10217  in
          failwith uu____10216
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10258)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10309,lbs),uu____10311)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10339 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10339
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10371 -> FStar_Pervasives_Native.None)
        | uu____10376 -> FStar_Pervasives_Native.None
  
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
        let uu____10400 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____10400
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____10423),uu____10424) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____10473 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10490 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____10490
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____10505 = lookup_qname env ftv  in
      match uu____10505 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10509) ->
          let uu____10554 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____10554 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10575,t),r) ->
               let uu____10590 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10590)
      | uu____10591 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____10598 = try_lookup_effect_lid env ftv  in
      match uu____10598 with
      | FStar_Pervasives_Native.None  ->
          let uu____10601 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10601 (FStar_Ident.range_of_lid ftv)
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
        let uu____10622 = lookup_qname env lid0  in
        match uu____10622 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10633);
                FStar_Syntax_Syntax.sigrng = uu____10634;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10636;
                FStar_Syntax_Syntax.sigattrs = uu____10637;_},FStar_Pervasives_Native.None
              ),uu____10638)
            ->
            let lid1 =
              let uu____10692 =
                let uu____10693 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10693
                 in
              FStar_Ident.set_lid_range lid uu____10692  in
            let uu____10694 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___76_10698  ->
                      match uu___76_10698 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10699 -> false))
               in
            if uu____10694
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10713 =
                      let uu____10714 =
                        let uu____10715 = get_range env  in
                        FStar_Range.string_of_range uu____10715  in
                      let uu____10716 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____10717 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10714 uu____10716 uu____10717
                       in
                    failwith uu____10713)
                  in
               match (binders, univs1) with
               | ([],uu____10724) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10741,uu____10742::uu____10743::uu____10744) ->
                   let uu____10749 =
                     let uu____10750 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____10751 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10750 uu____10751
                      in
                   failwith uu____10749
               | uu____10758 ->
                   let uu____10763 =
                     let uu____10768 =
                       let uu____10769 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____10769)  in
                     inst_tscheme_with uu____10768 insts  in
                   (match uu____10763 with
                    | (uu____10780,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____10783 =
                          let uu____10784 = FStar_Syntax_Subst.compress t1
                             in
                          uu____10784.FStar_Syntax_Syntax.n  in
                        (match uu____10783 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10831 -> failwith "Impossible")))
        | uu____10838 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10858 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____10858 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10871,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____10878 = find1 l2  in
            (match uu____10878 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____10885 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____10885 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10889 = find1 l  in
            (match uu____10889 with
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
      let uu____10903 = lookup_qname env l1  in
      match uu____10903 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10906;
              FStar_Syntax_Syntax.sigrng = uu____10907;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10909;
              FStar_Syntax_Syntax.sigattrs = uu____10910;_},uu____10911),uu____10912)
          -> q
      | uu____10963 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10976 =
          let uu____10977 =
            let uu____10978 = FStar_Util.string_of_int i  in
            let uu____10979 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10978 uu____10979
             in
          failwith uu____10977  in
        let uu____10980 = lookup_datacon env lid  in
        match uu____10980 with
        | (uu____10985,t) ->
            let uu____10987 =
              let uu____10988 = FStar_Syntax_Subst.compress t  in
              uu____10988.FStar_Syntax_Syntax.n  in
            (match uu____10987 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10992) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____11023 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____11023
                      FStar_Pervasives_Native.fst)
             | uu____11032 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11039 = lookup_qname env l  in
      match uu____11039 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11040,uu____11041,uu____11042);
              FStar_Syntax_Syntax.sigrng = uu____11043;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11045;
              FStar_Syntax_Syntax.sigattrs = uu____11046;_},uu____11047),uu____11048)
          ->
          FStar_Util.for_some
            (fun uu___77_11101  ->
               match uu___77_11101 with
               | FStar_Syntax_Syntax.Projector uu____11102 -> true
               | uu____11107 -> false) quals
      | uu____11108 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11115 = lookup_qname env lid  in
      match uu____11115 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11116,uu____11117,uu____11118,uu____11119,uu____11120,uu____11121);
              FStar_Syntax_Syntax.sigrng = uu____11122;
              FStar_Syntax_Syntax.sigquals = uu____11123;
              FStar_Syntax_Syntax.sigmeta = uu____11124;
              FStar_Syntax_Syntax.sigattrs = uu____11125;_},uu____11126),uu____11127)
          -> true
      | uu____11182 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11189 = lookup_qname env lid  in
      match uu____11189 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11190,uu____11191,uu____11192,uu____11193,uu____11194,uu____11195);
              FStar_Syntax_Syntax.sigrng = uu____11196;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11198;
              FStar_Syntax_Syntax.sigattrs = uu____11199;_},uu____11200),uu____11201)
          ->
          FStar_Util.for_some
            (fun uu___78_11262  ->
               match uu___78_11262 with
               | FStar_Syntax_Syntax.RecordType uu____11263 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11272 -> true
               | uu____11281 -> false) quals
      | uu____11282 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____11286,uu____11287);
            FStar_Syntax_Syntax.sigrng = uu____11288;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____11290;
            FStar_Syntax_Syntax.sigattrs = uu____11291;_},uu____11292),uu____11293)
        ->
        FStar_Util.for_some
          (fun uu___79_11350  ->
             match uu___79_11350 with
             | FStar_Syntax_Syntax.Action uu____11351 -> true
             | uu____11352 -> false) quals
    | uu____11353 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11360 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____11360
  
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
      let uu____11370 =
        let uu____11371 = FStar_Syntax_Util.un_uinst head1  in
        uu____11371.FStar_Syntax_Syntax.n  in
      match uu____11370 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11375 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11382 = lookup_qname env l  in
      match uu____11382 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11384),uu____11385) ->
          FStar_Util.for_some
            (fun uu___80_11433  ->
               match uu___80_11433 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11434 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11435 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11500 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11516) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11533 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11540 ->
                 FStar_Pervasives_Native.Some true
             | uu____11557 -> FStar_Pervasives_Native.Some false)
         in
      let uu____11558 =
        let uu____11561 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____11561 mapper  in
      match uu____11558 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____11607 = lookup_qname env lid  in
      match uu____11607 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11608,uu____11609,tps,uu____11611,uu____11612,uu____11613);
              FStar_Syntax_Syntax.sigrng = uu____11614;
              FStar_Syntax_Syntax.sigquals = uu____11615;
              FStar_Syntax_Syntax.sigmeta = uu____11616;
              FStar_Syntax_Syntax.sigattrs = uu____11617;_},uu____11618),uu____11619)
          -> FStar_List.length tps
      | uu____11682 ->
          let uu____11683 = name_not_found lid  in
          FStar_Errors.raise_error uu____11683 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____11727  ->
              match uu____11727 with
              | (d,uu____11735) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____11746 = effect_decl_opt env l  in
      match uu____11746 with
      | FStar_Pervasives_Native.None  ->
          let uu____11761 = name_not_found l  in
          FStar_Errors.raise_error uu____11761 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____11787  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11802  ->
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
            (let uu____11835 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11888  ->
                       match uu____11888 with
                       | (m1,m2,uu____11901,uu____11902,uu____11903) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____11835 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11920 =
                   let uu____11925 =
                     let uu____11926 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____11927 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11926
                       uu____11927
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____11925)
                    in
                 FStar_Errors.raise_error uu____11920 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11934,uu____11935,m3,j1,j2) -> (m3, j1, j2))
  
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
  'Auu____11972 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11972)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11999 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12025  ->
                match uu____12025 with
                | (d,uu____12031) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____11999 with
      | FStar_Pervasives_Native.None  ->
          let uu____12042 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12042
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12055 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12055 with
           | (uu____12066,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12076)::(wp,uu____12078)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12114 -> failwith "Impossible"))
  
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
                 let uu____12157 = get_range env  in
                 let uu____12158 =
                   let uu____12161 =
                     let uu____12162 =
                       let uu____12177 =
                         let uu____12180 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____12180]  in
                       (null_wp, uu____12177)  in
                     FStar_Syntax_Syntax.Tm_app uu____12162  in
                   FStar_Syntax_Syntax.mk uu____12161  in
                 uu____12158 FStar_Pervasives_Native.None uu____12157  in
               let uu____12186 =
                 let uu____12187 =
                   let uu____12196 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____12196]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12187;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____12186)
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___96_12205 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___96_12205.order);
              joins = (uu___96_12205.joins)
            }  in
          let uu___97_12214 = env  in
          {
            solver = (uu___97_12214.solver);
            range = (uu___97_12214.range);
            curmodule = (uu___97_12214.curmodule);
            gamma = (uu___97_12214.gamma);
            gamma_cache = (uu___97_12214.gamma_cache);
            modules = (uu___97_12214.modules);
            expected_typ = (uu___97_12214.expected_typ);
            sigtab = (uu___97_12214.sigtab);
            is_pattern = (uu___97_12214.is_pattern);
            instantiate_imp = (uu___97_12214.instantiate_imp);
            effects;
            generalize = (uu___97_12214.generalize);
            letrecs = (uu___97_12214.letrecs);
            top_level = (uu___97_12214.top_level);
            check_uvars = (uu___97_12214.check_uvars);
            use_eq = (uu___97_12214.use_eq);
            is_iface = (uu___97_12214.is_iface);
            admit = (uu___97_12214.admit);
            lax = (uu___97_12214.lax);
            lax_universes = (uu___97_12214.lax_universes);
            failhard = (uu___97_12214.failhard);
            nosynth = (uu___97_12214.nosynth);
            tc_term = (uu___97_12214.tc_term);
            type_of = (uu___97_12214.type_of);
            universe_of = (uu___97_12214.universe_of);
            check_type_of = (uu___97_12214.check_type_of);
            use_bv_sorts = (uu___97_12214.use_bv_sorts);
            qtbl_name_and_index = (uu___97_12214.qtbl_name_and_index);
            proof_ns = (uu___97_12214.proof_ns);
            synth = (uu___97_12214.synth);
            is_native_tactic = (uu___97_12214.is_native_tactic);
            identifier_info = (uu___97_12214.identifier_info);
            tc_hooks = (uu___97_12214.tc_hooks);
            dsenv = (uu___97_12214.dsenv);
            dep_graph = (uu___97_12214.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12234 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12234  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12348 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12349 = l1 u t wp e  in
                                l2 u t uu____12348 uu____12349))
                | uu____12350 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12398 = inst_tscheme_with lift_t [u]  in
            match uu____12398 with
            | (uu____12405,lift_t1) ->
                let uu____12407 =
                  let uu____12410 =
                    let uu____12411 =
                      let uu____12426 =
                        let uu____12429 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12430 =
                          let uu____12433 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12433]  in
                        uu____12429 :: uu____12430  in
                      (lift_t1, uu____12426)  in
                    FStar_Syntax_Syntax.Tm_app uu____12411  in
                  FStar_Syntax_Syntax.mk uu____12410  in
                uu____12407 FStar_Pervasives_Native.None
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
            let uu____12483 = inst_tscheme_with lift_t [u]  in
            match uu____12483 with
            | (uu____12490,lift_t1) ->
                let uu____12492 =
                  let uu____12495 =
                    let uu____12496 =
                      let uu____12511 =
                        let uu____12514 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12515 =
                          let uu____12518 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12519 =
                            let uu____12522 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12522]  in
                          uu____12518 :: uu____12519  in
                        uu____12514 :: uu____12515  in
                      (lift_t1, uu____12511)  in
                    FStar_Syntax_Syntax.Tm_app uu____12496  in
                  FStar_Syntax_Syntax.mk uu____12495  in
                uu____12492 FStar_Pervasives_Native.None
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
              let uu____12564 =
                let uu____12565 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____12565
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____12564  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____12569 =
              let uu____12570 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____12570  in
            let uu____12571 =
              let uu____12572 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12594 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____12594)
                 in
              FStar_Util.dflt "none" uu____12572  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12569
              uu____12571
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12620  ->
                    match uu____12620 with
                    | (e,uu____12628) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____12647 =
            match uu____12647 with
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
              let uu____12685 =
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
                                    (let uu____12706 =
                                       let uu____12715 =
                                         find_edge order1 (i, k)  in
                                       let uu____12718 =
                                         find_edge order1 (k, j)  in
                                       (uu____12715, uu____12718)  in
                                     match uu____12706 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12733 =
                                           compose_edges e1 e2  in
                                         [uu____12733]
                                     | uu____12734 -> [])))))
                 in
              FStar_List.append order1 uu____12685  in
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
                   let uu____12764 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12766 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____12766
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____12764
                   then
                     let uu____12771 =
                       let uu____12776 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12776)
                        in
                     let uu____12777 = get_range env  in
                     FStar_Errors.raise_error uu____12771 uu____12777
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
                                            let uu____12902 =
                                              let uu____12911 =
                                                find_edge order2 (i, k)  in
                                              let uu____12914 =
                                                find_edge order2 (j, k)  in
                                              (uu____12911, uu____12914)  in
                                            match uu____12902 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12956,uu____12957)
                                                     ->
                                                     let uu____12964 =
                                                       let uu____12969 =
                                                         let uu____12970 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12970
                                                          in
                                                       let uu____12973 =
                                                         let uu____12974 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12974
                                                          in
                                                       (uu____12969,
                                                         uu____12973)
                                                        in
                                                     (match uu____12964 with
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
                                            | uu____13009 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___98_13082 = env.effects  in
              { decls = (uu___98_13082.decls); order = order2; joins }  in
            let uu___99_13083 = env  in
            {
              solver = (uu___99_13083.solver);
              range = (uu___99_13083.range);
              curmodule = (uu___99_13083.curmodule);
              gamma = (uu___99_13083.gamma);
              gamma_cache = (uu___99_13083.gamma_cache);
              modules = (uu___99_13083.modules);
              expected_typ = (uu___99_13083.expected_typ);
              sigtab = (uu___99_13083.sigtab);
              is_pattern = (uu___99_13083.is_pattern);
              instantiate_imp = (uu___99_13083.instantiate_imp);
              effects;
              generalize = (uu___99_13083.generalize);
              letrecs = (uu___99_13083.letrecs);
              top_level = (uu___99_13083.top_level);
              check_uvars = (uu___99_13083.check_uvars);
              use_eq = (uu___99_13083.use_eq);
              is_iface = (uu___99_13083.is_iface);
              admit = (uu___99_13083.admit);
              lax = (uu___99_13083.lax);
              lax_universes = (uu___99_13083.lax_universes);
              failhard = (uu___99_13083.failhard);
              nosynth = (uu___99_13083.nosynth);
              tc_term = (uu___99_13083.tc_term);
              type_of = (uu___99_13083.type_of);
              universe_of = (uu___99_13083.universe_of);
              check_type_of = (uu___99_13083.check_type_of);
              use_bv_sorts = (uu___99_13083.use_bv_sorts);
              qtbl_name_and_index = (uu___99_13083.qtbl_name_and_index);
              proof_ns = (uu___99_13083.proof_ns);
              synth = (uu___99_13083.synth);
              is_native_tactic = (uu___99_13083.is_native_tactic);
              identifier_info = (uu___99_13083.identifier_info);
              tc_hooks = (uu___99_13083.tc_hooks);
              dsenv = (uu___99_13083.dsenv);
              dep_graph = (uu___99_13083.dep_graph)
            }))
      | uu____13084 -> env
  
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
        | uu____13108 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13116 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13116 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13133 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13133 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13151 =
                     let uu____13156 =
                       let uu____13157 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13162 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13169 =
                         let uu____13170 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13170  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13157 uu____13162 uu____13169
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13156)
                      in
                   FStar_Errors.raise_error uu____13151
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13175 =
                     let uu____13184 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13184 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13201  ->
                        fun uu____13202  ->
                          match (uu____13201, uu____13202) with
                          | ((x,uu____13224),(t,uu____13226)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13175
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13245 =
                     let uu___100_13246 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___100_13246.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___100_13246.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___100_13246.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___100_13246.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13245
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
          let uu____13268 = effect_decl_opt env effect_name  in
          match uu____13268 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13301 =
                only_reifiable &&
                  (let uu____13303 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13303)
                 in
              if uu____13301
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13319 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13338 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13367 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13367
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13368 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13368
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13378 =
                       let uu____13381 = get_range env  in
                       let uu____13382 =
                         let uu____13385 =
                           let uu____13386 =
                             let uu____13401 =
                               let uu____13404 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13404; wp]  in
                             (repr, uu____13401)  in
                           FStar_Syntax_Syntax.Tm_app uu____13386  in
                         FStar_Syntax_Syntax.mk uu____13385  in
                       uu____13382 FStar_Pervasives_Native.None uu____13381
                        in
                     FStar_Pervasives_Native.Some uu____13378)
  
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
          let uu____13450 =
            let uu____13455 =
              let uu____13456 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13456
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13455)  in
          let uu____13457 = get_range env  in
          FStar_Errors.raise_error uu____13450 uu____13457  in
        let uu____13458 = effect_repr_aux true env c u_c  in
        match uu____13458 with
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
      | uu____13492 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____13499 =
        let uu____13500 = FStar_Syntax_Subst.compress t  in
        uu____13500.FStar_Syntax_Syntax.n  in
      match uu____13499 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13503,c) ->
          is_reifiable_comp env c
      | uu____13521 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13543)::uu____13544 -> x :: rest
        | (Binding_sig_inst uu____13553)::uu____13554 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13569 = push1 x rest1  in local :: uu____13569
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___101_13573 = env  in
       let uu____13574 = push1 s env.gamma  in
       {
         solver = (uu___101_13573.solver);
         range = (uu___101_13573.range);
         curmodule = (uu___101_13573.curmodule);
         gamma = uu____13574;
         gamma_cache = (uu___101_13573.gamma_cache);
         modules = (uu___101_13573.modules);
         expected_typ = (uu___101_13573.expected_typ);
         sigtab = (uu___101_13573.sigtab);
         is_pattern = (uu___101_13573.is_pattern);
         instantiate_imp = (uu___101_13573.instantiate_imp);
         effects = (uu___101_13573.effects);
         generalize = (uu___101_13573.generalize);
         letrecs = (uu___101_13573.letrecs);
         top_level = (uu___101_13573.top_level);
         check_uvars = (uu___101_13573.check_uvars);
         use_eq = (uu___101_13573.use_eq);
         is_iface = (uu___101_13573.is_iface);
         admit = (uu___101_13573.admit);
         lax = (uu___101_13573.lax);
         lax_universes = (uu___101_13573.lax_universes);
         failhard = (uu___101_13573.failhard);
         nosynth = (uu___101_13573.nosynth);
         tc_term = (uu___101_13573.tc_term);
         type_of = (uu___101_13573.type_of);
         universe_of = (uu___101_13573.universe_of);
         check_type_of = (uu___101_13573.check_type_of);
         use_bv_sorts = (uu___101_13573.use_bv_sorts);
         qtbl_name_and_index = (uu___101_13573.qtbl_name_and_index);
         proof_ns = (uu___101_13573.proof_ns);
         synth = (uu___101_13573.synth);
         is_native_tactic = (uu___101_13573.is_native_tactic);
         identifier_info = (uu___101_13573.identifier_info);
         tc_hooks = (uu___101_13573.tc_hooks);
         dsenv = (uu___101_13573.dsenv);
         dep_graph = (uu___101_13573.dep_graph)
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
      let uu___102_13604 = env  in
      {
        solver = (uu___102_13604.solver);
        range = (uu___102_13604.range);
        curmodule = (uu___102_13604.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___102_13604.gamma_cache);
        modules = (uu___102_13604.modules);
        expected_typ = (uu___102_13604.expected_typ);
        sigtab = (uu___102_13604.sigtab);
        is_pattern = (uu___102_13604.is_pattern);
        instantiate_imp = (uu___102_13604.instantiate_imp);
        effects = (uu___102_13604.effects);
        generalize = (uu___102_13604.generalize);
        letrecs = (uu___102_13604.letrecs);
        top_level = (uu___102_13604.top_level);
        check_uvars = (uu___102_13604.check_uvars);
        use_eq = (uu___102_13604.use_eq);
        is_iface = (uu___102_13604.is_iface);
        admit = (uu___102_13604.admit);
        lax = (uu___102_13604.lax);
        lax_universes = (uu___102_13604.lax_universes);
        failhard = (uu___102_13604.failhard);
        nosynth = (uu___102_13604.nosynth);
        tc_term = (uu___102_13604.tc_term);
        type_of = (uu___102_13604.type_of);
        universe_of = (uu___102_13604.universe_of);
        check_type_of = (uu___102_13604.check_type_of);
        use_bv_sorts = (uu___102_13604.use_bv_sorts);
        qtbl_name_and_index = (uu___102_13604.qtbl_name_and_index);
        proof_ns = (uu___102_13604.proof_ns);
        synth = (uu___102_13604.synth);
        is_native_tactic = (uu___102_13604.is_native_tactic);
        identifier_info = (uu___102_13604.identifier_info);
        tc_hooks = (uu___102_13604.tc_hooks);
        dsenv = (uu___102_13604.dsenv);
        dep_graph = (uu___102_13604.dep_graph)
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
            (let uu___103_13635 = env  in
             {
               solver = (uu___103_13635.solver);
               range = (uu___103_13635.range);
               curmodule = (uu___103_13635.curmodule);
               gamma = rest;
               gamma_cache = (uu___103_13635.gamma_cache);
               modules = (uu___103_13635.modules);
               expected_typ = (uu___103_13635.expected_typ);
               sigtab = (uu___103_13635.sigtab);
               is_pattern = (uu___103_13635.is_pattern);
               instantiate_imp = (uu___103_13635.instantiate_imp);
               effects = (uu___103_13635.effects);
               generalize = (uu___103_13635.generalize);
               letrecs = (uu___103_13635.letrecs);
               top_level = (uu___103_13635.top_level);
               check_uvars = (uu___103_13635.check_uvars);
               use_eq = (uu___103_13635.use_eq);
               is_iface = (uu___103_13635.is_iface);
               admit = (uu___103_13635.admit);
               lax = (uu___103_13635.lax);
               lax_universes = (uu___103_13635.lax_universes);
               failhard = (uu___103_13635.failhard);
               nosynth = (uu___103_13635.nosynth);
               tc_term = (uu___103_13635.tc_term);
               type_of = (uu___103_13635.type_of);
               universe_of = (uu___103_13635.universe_of);
               check_type_of = (uu___103_13635.check_type_of);
               use_bv_sorts = (uu___103_13635.use_bv_sorts);
               qtbl_name_and_index = (uu___103_13635.qtbl_name_and_index);
               proof_ns = (uu___103_13635.proof_ns);
               synth = (uu___103_13635.synth);
               is_native_tactic = (uu___103_13635.is_native_tactic);
               identifier_info = (uu___103_13635.identifier_info);
               tc_hooks = (uu___103_13635.tc_hooks);
               dsenv = (uu___103_13635.dsenv);
               dep_graph = (uu___103_13635.dep_graph)
             }))
    | uu____13636 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13658  ->
             match uu____13658 with | (x,uu____13664) -> push_bv env1 x) env
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
            let uu___104_13692 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___104_13692.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___104_13692.FStar_Syntax_Syntax.index);
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
      (let uu___105_13722 = env  in
       {
         solver = (uu___105_13722.solver);
         range = (uu___105_13722.range);
         curmodule = (uu___105_13722.curmodule);
         gamma = [];
         gamma_cache = (uu___105_13722.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___105_13722.sigtab);
         is_pattern = (uu___105_13722.is_pattern);
         instantiate_imp = (uu___105_13722.instantiate_imp);
         effects = (uu___105_13722.effects);
         generalize = (uu___105_13722.generalize);
         letrecs = (uu___105_13722.letrecs);
         top_level = (uu___105_13722.top_level);
         check_uvars = (uu___105_13722.check_uvars);
         use_eq = (uu___105_13722.use_eq);
         is_iface = (uu___105_13722.is_iface);
         admit = (uu___105_13722.admit);
         lax = (uu___105_13722.lax);
         lax_universes = (uu___105_13722.lax_universes);
         failhard = (uu___105_13722.failhard);
         nosynth = (uu___105_13722.nosynth);
         tc_term = (uu___105_13722.tc_term);
         type_of = (uu___105_13722.type_of);
         universe_of = (uu___105_13722.universe_of);
         check_type_of = (uu___105_13722.check_type_of);
         use_bv_sorts = (uu___105_13722.use_bv_sorts);
         qtbl_name_and_index = (uu___105_13722.qtbl_name_and_index);
         proof_ns = (uu___105_13722.proof_ns);
         synth = (uu___105_13722.synth);
         is_native_tactic = (uu___105_13722.is_native_tactic);
         identifier_info = (uu___105_13722.identifier_info);
         tc_hooks = (uu___105_13722.tc_hooks);
         dsenv = (uu___105_13722.dsenv);
         dep_graph = (uu___105_13722.dep_graph)
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
        let uu____13754 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____13754 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____13782 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____13782)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___106_13795 = env  in
      {
        solver = (uu___106_13795.solver);
        range = (uu___106_13795.range);
        curmodule = (uu___106_13795.curmodule);
        gamma = (uu___106_13795.gamma);
        gamma_cache = (uu___106_13795.gamma_cache);
        modules = (uu___106_13795.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___106_13795.sigtab);
        is_pattern = (uu___106_13795.is_pattern);
        instantiate_imp = (uu___106_13795.instantiate_imp);
        effects = (uu___106_13795.effects);
        generalize = (uu___106_13795.generalize);
        letrecs = (uu___106_13795.letrecs);
        top_level = (uu___106_13795.top_level);
        check_uvars = (uu___106_13795.check_uvars);
        use_eq = false;
        is_iface = (uu___106_13795.is_iface);
        admit = (uu___106_13795.admit);
        lax = (uu___106_13795.lax);
        lax_universes = (uu___106_13795.lax_universes);
        failhard = (uu___106_13795.failhard);
        nosynth = (uu___106_13795.nosynth);
        tc_term = (uu___106_13795.tc_term);
        type_of = (uu___106_13795.type_of);
        universe_of = (uu___106_13795.universe_of);
        check_type_of = (uu___106_13795.check_type_of);
        use_bv_sorts = (uu___106_13795.use_bv_sorts);
        qtbl_name_and_index = (uu___106_13795.qtbl_name_and_index);
        proof_ns = (uu___106_13795.proof_ns);
        synth = (uu___106_13795.synth);
        is_native_tactic = (uu___106_13795.is_native_tactic);
        identifier_info = (uu___106_13795.identifier_info);
        tc_hooks = (uu___106_13795.tc_hooks);
        dsenv = (uu___106_13795.dsenv);
        dep_graph = (uu___106_13795.dep_graph)
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
    let uu____13819 = expected_typ env_  in
    ((let uu___107_13825 = env_  in
      {
        solver = (uu___107_13825.solver);
        range = (uu___107_13825.range);
        curmodule = (uu___107_13825.curmodule);
        gamma = (uu___107_13825.gamma);
        gamma_cache = (uu___107_13825.gamma_cache);
        modules = (uu___107_13825.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___107_13825.sigtab);
        is_pattern = (uu___107_13825.is_pattern);
        instantiate_imp = (uu___107_13825.instantiate_imp);
        effects = (uu___107_13825.effects);
        generalize = (uu___107_13825.generalize);
        letrecs = (uu___107_13825.letrecs);
        top_level = (uu___107_13825.top_level);
        check_uvars = (uu___107_13825.check_uvars);
        use_eq = false;
        is_iface = (uu___107_13825.is_iface);
        admit = (uu___107_13825.admit);
        lax = (uu___107_13825.lax);
        lax_universes = (uu___107_13825.lax_universes);
        failhard = (uu___107_13825.failhard);
        nosynth = (uu___107_13825.nosynth);
        tc_term = (uu___107_13825.tc_term);
        type_of = (uu___107_13825.type_of);
        universe_of = (uu___107_13825.universe_of);
        check_type_of = (uu___107_13825.check_type_of);
        use_bv_sorts = (uu___107_13825.use_bv_sorts);
        qtbl_name_and_index = (uu___107_13825.qtbl_name_and_index);
        proof_ns = (uu___107_13825.proof_ns);
        synth = (uu___107_13825.synth);
        is_native_tactic = (uu___107_13825.is_native_tactic);
        identifier_info = (uu___107_13825.identifier_info);
        tc_hooks = (uu___107_13825.tc_hooks);
        dsenv = (uu___107_13825.dsenv);
        dep_graph = (uu___107_13825.dep_graph)
      }), uu____13819)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13838 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___81_13848  ->
                    match uu___81_13848 with
                    | Binding_sig (uu____13851,se) -> [se]
                    | uu____13857 -> []))
             in
          FStar_All.pipe_right uu____13838 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___108_13864 = env  in
       {
         solver = (uu___108_13864.solver);
         range = (uu___108_13864.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___108_13864.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___108_13864.expected_typ);
         sigtab = (uu___108_13864.sigtab);
         is_pattern = (uu___108_13864.is_pattern);
         instantiate_imp = (uu___108_13864.instantiate_imp);
         effects = (uu___108_13864.effects);
         generalize = (uu___108_13864.generalize);
         letrecs = (uu___108_13864.letrecs);
         top_level = (uu___108_13864.top_level);
         check_uvars = (uu___108_13864.check_uvars);
         use_eq = (uu___108_13864.use_eq);
         is_iface = (uu___108_13864.is_iface);
         admit = (uu___108_13864.admit);
         lax = (uu___108_13864.lax);
         lax_universes = (uu___108_13864.lax_universes);
         failhard = (uu___108_13864.failhard);
         nosynth = (uu___108_13864.nosynth);
         tc_term = (uu___108_13864.tc_term);
         type_of = (uu___108_13864.type_of);
         universe_of = (uu___108_13864.universe_of);
         check_type_of = (uu___108_13864.check_type_of);
         use_bv_sorts = (uu___108_13864.use_bv_sorts);
         qtbl_name_and_index = (uu___108_13864.qtbl_name_and_index);
         proof_ns = (uu___108_13864.proof_ns);
         synth = (uu___108_13864.synth);
         is_native_tactic = (uu___108_13864.is_native_tactic);
         identifier_info = (uu___108_13864.identifier_info);
         tc_hooks = (uu___108_13864.tc_hooks);
         dsenv = (uu___108_13864.dsenv);
         dep_graph = (uu___108_13864.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13945)::tl1 -> aux out tl1
      | (Binding_lid (uu____13949,(uu____13950,t)))::tl1 ->
          let uu____13965 =
            let uu____13972 = FStar_Syntax_Free.uvars t  in
            ext out uu____13972  in
          aux uu____13965 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13979;
            FStar_Syntax_Syntax.index = uu____13980;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13987 =
            let uu____13994 = FStar_Syntax_Free.uvars t  in
            ext out uu____13994  in
          aux uu____13987 tl1
      | (Binding_sig uu____14001)::uu____14002 -> out
      | (Binding_sig_inst uu____14011)::uu____14012 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14067)::tl1 -> aux out tl1
      | (Binding_univ uu____14079)::tl1 -> aux out tl1
      | (Binding_lid (uu____14083,(uu____14084,t)))::tl1 ->
          let uu____14099 =
            let uu____14102 = FStar_Syntax_Free.univs t  in
            ext out uu____14102  in
          aux uu____14099 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14105;
            FStar_Syntax_Syntax.index = uu____14106;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14113 =
            let uu____14116 = FStar_Syntax_Free.univs t  in
            ext out uu____14116  in
          aux uu____14113 tl1
      | (Binding_sig uu____14119)::uu____14120 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14173)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14189 = FStar_Util.fifo_set_add uname out  in
          aux uu____14189 tl1
      | (Binding_lid (uu____14192,(uu____14193,t)))::tl1 ->
          let uu____14208 =
            let uu____14211 = FStar_Syntax_Free.univnames t  in
            ext out uu____14211  in
          aux uu____14208 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14214;
            FStar_Syntax_Syntax.index = uu____14215;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14222 =
            let uu____14225 = FStar_Syntax_Free.univnames t  in
            ext out uu____14225  in
          aux uu____14222 tl1
      | (Binding_sig uu____14228)::uu____14229 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___82_14253  ->
            match uu___82_14253 with
            | Binding_var x -> [x]
            | Binding_lid uu____14257 -> []
            | Binding_sig uu____14262 -> []
            | Binding_univ uu____14269 -> []
            | Binding_sig_inst uu____14270 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____14286 =
      let uu____14289 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14289
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14286 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____14311 =
      let uu____14312 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___83_14322  ->
                match uu___83_14322 with
                | Binding_var x ->
                    let uu____14324 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14324
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14327) ->
                    let uu____14328 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14328
                | Binding_sig (ls,uu____14330) ->
                    let uu____14335 =
                      let uu____14336 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14336
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14335
                | Binding_sig_inst (ls,uu____14346,uu____14347) ->
                    let uu____14352 =
                      let uu____14353 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14353
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14352))
         in
      FStar_All.pipe_right uu____14312 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14311 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____14370 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14370
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14398  ->
                 fun uu____14399  ->
                   match (uu____14398, uu____14399) with
                   | ((b1,uu____14417),(b2,uu____14419)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___84_14461  ->
    match uu___84_14461 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14462 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___85_14480  ->
             match uu___85_14480 with
             | Binding_sig (lids,uu____14486) -> FStar_List.append lids keys
             | uu____14491 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14497  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14531) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14550,uu____14551) -> false  in
      let uu____14560 =
        FStar_List.tryFind
          (fun uu____14578  ->
             match uu____14578 with | (p,uu____14586) -> list_prefix p path)
          env.proof_ns
         in
      match uu____14560 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14597,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14615 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____14615
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___109_14627 = e  in
        {
          solver = (uu___109_14627.solver);
          range = (uu___109_14627.range);
          curmodule = (uu___109_14627.curmodule);
          gamma = (uu___109_14627.gamma);
          gamma_cache = (uu___109_14627.gamma_cache);
          modules = (uu___109_14627.modules);
          expected_typ = (uu___109_14627.expected_typ);
          sigtab = (uu___109_14627.sigtab);
          is_pattern = (uu___109_14627.is_pattern);
          instantiate_imp = (uu___109_14627.instantiate_imp);
          effects = (uu___109_14627.effects);
          generalize = (uu___109_14627.generalize);
          letrecs = (uu___109_14627.letrecs);
          top_level = (uu___109_14627.top_level);
          check_uvars = (uu___109_14627.check_uvars);
          use_eq = (uu___109_14627.use_eq);
          is_iface = (uu___109_14627.is_iface);
          admit = (uu___109_14627.admit);
          lax = (uu___109_14627.lax);
          lax_universes = (uu___109_14627.lax_universes);
          failhard = (uu___109_14627.failhard);
          nosynth = (uu___109_14627.nosynth);
          tc_term = (uu___109_14627.tc_term);
          type_of = (uu___109_14627.type_of);
          universe_of = (uu___109_14627.universe_of);
          check_type_of = (uu___109_14627.check_type_of);
          use_bv_sorts = (uu___109_14627.use_bv_sorts);
          qtbl_name_and_index = (uu___109_14627.qtbl_name_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___109_14627.synth);
          is_native_tactic = (uu___109_14627.is_native_tactic);
          identifier_info = (uu___109_14627.identifier_info);
          tc_hooks = (uu___109_14627.tc_hooks);
          dsenv = (uu___109_14627.dsenv);
          dep_graph = (uu___109_14627.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___110_14653 = e  in
      {
        solver = (uu___110_14653.solver);
        range = (uu___110_14653.range);
        curmodule = (uu___110_14653.curmodule);
        gamma = (uu___110_14653.gamma);
        gamma_cache = (uu___110_14653.gamma_cache);
        modules = (uu___110_14653.modules);
        expected_typ = (uu___110_14653.expected_typ);
        sigtab = (uu___110_14653.sigtab);
        is_pattern = (uu___110_14653.is_pattern);
        instantiate_imp = (uu___110_14653.instantiate_imp);
        effects = (uu___110_14653.effects);
        generalize = (uu___110_14653.generalize);
        letrecs = (uu___110_14653.letrecs);
        top_level = (uu___110_14653.top_level);
        check_uvars = (uu___110_14653.check_uvars);
        use_eq = (uu___110_14653.use_eq);
        is_iface = (uu___110_14653.is_iface);
        admit = (uu___110_14653.admit);
        lax = (uu___110_14653.lax);
        lax_universes = (uu___110_14653.lax_universes);
        failhard = (uu___110_14653.failhard);
        nosynth = (uu___110_14653.nosynth);
        tc_term = (uu___110_14653.tc_term);
        type_of = (uu___110_14653.type_of);
        universe_of = (uu___110_14653.universe_of);
        check_type_of = (uu___110_14653.check_type_of);
        use_bv_sorts = (uu___110_14653.use_bv_sorts);
        qtbl_name_and_index = (uu___110_14653.qtbl_name_and_index);
        proof_ns = ns;
        synth = (uu___110_14653.synth);
        is_native_tactic = (uu___110_14653.is_native_tactic);
        identifier_info = (uu___110_14653.identifier_info);
        tc_hooks = (uu___110_14653.tc_hooks);
        dsenv = (uu___110_14653.dsenv);
        dep_graph = (uu___110_14653.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____14664 = FStar_Syntax_Free.names t  in
      let uu____14667 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14664 uu____14667
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____14684 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____14684
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14690 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____14690
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____14705 =
      match uu____14705 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14721 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____14721)
       in
    let uu____14723 =
      let uu____14726 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____14726 FStar_List.rev  in
    FStar_All.pipe_right uu____14723 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____14743  -> ());
    push = (fun uu____14745  -> ());
    pop = (fun uu____14747  -> ());
    encode_modul = (fun uu____14750  -> fun uu____14751  -> ());
    encode_sig = (fun uu____14754  -> fun uu____14755  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14761 =
             let uu____14768 = FStar_Options.peek ()  in (e, g, uu____14768)
              in
           [uu____14761]);
    solve = (fun uu____14784  -> fun uu____14785  -> fun uu____14786  -> ());
    finish = (fun uu____14792  -> ());
    refresh = (fun uu____14794  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___111_14798 = en  in
    let uu____14799 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____14802 = FStar_Util.smap_copy en.sigtab  in
    let uu____14805 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___111_14798.solver);
      range = (uu___111_14798.range);
      curmodule = (uu___111_14798.curmodule);
      gamma = (uu___111_14798.gamma);
      gamma_cache = uu____14799;
      modules = (uu___111_14798.modules);
      expected_typ = (uu___111_14798.expected_typ);
      sigtab = uu____14802;
      is_pattern = (uu___111_14798.is_pattern);
      instantiate_imp = (uu___111_14798.instantiate_imp);
      effects = (uu___111_14798.effects);
      generalize = (uu___111_14798.generalize);
      letrecs = (uu___111_14798.letrecs);
      top_level = (uu___111_14798.top_level);
      check_uvars = (uu___111_14798.check_uvars);
      use_eq = (uu___111_14798.use_eq);
      is_iface = (uu___111_14798.is_iface);
      admit = (uu___111_14798.admit);
      lax = (uu___111_14798.lax);
      lax_universes = (uu___111_14798.lax_universes);
      failhard = (uu___111_14798.failhard);
      nosynth = (uu___111_14798.nosynth);
      tc_term = (uu___111_14798.tc_term);
      type_of = (uu___111_14798.type_of);
      universe_of = (uu___111_14798.universe_of);
      check_type_of = (uu___111_14798.check_type_of);
      use_bv_sorts = (uu___111_14798.use_bv_sorts);
      qtbl_name_and_index = (uu___111_14798.qtbl_name_and_index);
      proof_ns = (uu___111_14798.proof_ns);
      synth = (uu___111_14798.synth);
      is_native_tactic = (uu___111_14798.is_native_tactic);
      identifier_info = (uu___111_14798.identifier_info);
      tc_hooks = (uu___111_14798.tc_hooks);
      dsenv = uu____14805;
      dep_graph = (uu___111_14798.dep_graph)
    }
  