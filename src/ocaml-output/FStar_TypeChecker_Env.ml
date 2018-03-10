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
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
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
        splice = __fname__splice;
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
        splice = __fname__splice;
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
        splice = __fname__splice;
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
        splice = __fname__splice;
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
        splice = __fname__splice;
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
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
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
        splice = __fname__splice;
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
           (fun uu___71_6141  ->
              match uu___71_6141 with
              | Binding_var x ->
                  let y =
                    let uu____6144 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____6144  in
                  let uu____6145 =
                    let uu____6146 = FStar_Syntax_Subst.compress y  in
                    uu____6146.FStar_Syntax_Syntax.n  in
                  (match uu____6145 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____6150 =
                         let uu___86_6151 = y1  in
                         let uu____6152 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___86_6151.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___86_6151.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____6152
                         }  in
                       Binding_var uu____6150
                   | uu____6155 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___87_6163 = env  in
      let uu____6164 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___87_6163.solver);
        range = (uu___87_6163.range);
        curmodule = (uu___87_6163.curmodule);
        gamma = uu____6164;
        gamma_cache = (uu___87_6163.gamma_cache);
        modules = (uu___87_6163.modules);
        expected_typ = (uu___87_6163.expected_typ);
        sigtab = (uu___87_6163.sigtab);
        is_pattern = (uu___87_6163.is_pattern);
        instantiate_imp = (uu___87_6163.instantiate_imp);
        effects = (uu___87_6163.effects);
        generalize = (uu___87_6163.generalize);
        letrecs = (uu___87_6163.letrecs);
        top_level = (uu___87_6163.top_level);
        check_uvars = (uu___87_6163.check_uvars);
        use_eq = (uu___87_6163.use_eq);
        is_iface = (uu___87_6163.is_iface);
        admit = (uu___87_6163.admit);
        lax = (uu___87_6163.lax);
        lax_universes = (uu___87_6163.lax_universes);
        failhard = (uu___87_6163.failhard);
        nosynth = (uu___87_6163.nosynth);
        tc_term = (uu___87_6163.tc_term);
        type_of = (uu___87_6163.type_of);
        universe_of = (uu___87_6163.universe_of);
        check_type_of = (uu___87_6163.check_type_of);
        use_bv_sorts = (uu___87_6163.use_bv_sorts);
        qtbl_name_and_index = (uu___87_6163.qtbl_name_and_index);
        proof_ns = (uu___87_6163.proof_ns);
        synth = (uu___87_6163.synth);
        splice = (uu___87_6163.splice);
        is_native_tactic = (uu___87_6163.is_native_tactic);
        identifier_info = (uu___87_6163.identifier_info);
        tc_hooks = (uu___87_6163.tc_hooks);
        dsenv = (uu___87_6163.dsenv);
        dep_graph = (uu___87_6163.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____6171  -> fun uu____6172  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___88_6182 = env  in
      {
        solver = (uu___88_6182.solver);
        range = (uu___88_6182.range);
        curmodule = (uu___88_6182.curmodule);
        gamma = (uu___88_6182.gamma);
        gamma_cache = (uu___88_6182.gamma_cache);
        modules = (uu___88_6182.modules);
        expected_typ = (uu___88_6182.expected_typ);
        sigtab = (uu___88_6182.sigtab);
        is_pattern = (uu___88_6182.is_pattern);
        instantiate_imp = (uu___88_6182.instantiate_imp);
        effects = (uu___88_6182.effects);
        generalize = (uu___88_6182.generalize);
        letrecs = (uu___88_6182.letrecs);
        top_level = (uu___88_6182.top_level);
        check_uvars = (uu___88_6182.check_uvars);
        use_eq = (uu___88_6182.use_eq);
        is_iface = (uu___88_6182.is_iface);
        admit = (uu___88_6182.admit);
        lax = (uu___88_6182.lax);
        lax_universes = (uu___88_6182.lax_universes);
        failhard = (uu___88_6182.failhard);
        nosynth = (uu___88_6182.nosynth);
        tc_term = (uu___88_6182.tc_term);
        type_of = (uu___88_6182.type_of);
        universe_of = (uu___88_6182.universe_of);
        check_type_of = (uu___88_6182.check_type_of);
        use_bv_sorts = (uu___88_6182.use_bv_sorts);
        qtbl_name_and_index = (uu___88_6182.qtbl_name_and_index);
        proof_ns = (uu___88_6182.proof_ns);
        synth = (uu___88_6182.synth);
        splice = (uu___88_6182.splice);
        is_native_tactic = (uu___88_6182.is_native_tactic);
        identifier_info = (uu___88_6182.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___88_6182.dsenv);
        dep_graph = (uu___88_6182.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___89_6189 = e  in
      {
        solver = (uu___89_6189.solver);
        range = (uu___89_6189.range);
        curmodule = (uu___89_6189.curmodule);
        gamma = (uu___89_6189.gamma);
        gamma_cache = (uu___89_6189.gamma_cache);
        modules = (uu___89_6189.modules);
        expected_typ = (uu___89_6189.expected_typ);
        sigtab = (uu___89_6189.sigtab);
        is_pattern = (uu___89_6189.is_pattern);
        instantiate_imp = (uu___89_6189.instantiate_imp);
        effects = (uu___89_6189.effects);
        generalize = (uu___89_6189.generalize);
        letrecs = (uu___89_6189.letrecs);
        top_level = (uu___89_6189.top_level);
        check_uvars = (uu___89_6189.check_uvars);
        use_eq = (uu___89_6189.use_eq);
        is_iface = (uu___89_6189.is_iface);
        admit = (uu___89_6189.admit);
        lax = (uu___89_6189.lax);
        lax_universes = (uu___89_6189.lax_universes);
        failhard = (uu___89_6189.failhard);
        nosynth = (uu___89_6189.nosynth);
        tc_term = (uu___89_6189.tc_term);
        type_of = (uu___89_6189.type_of);
        universe_of = (uu___89_6189.universe_of);
        check_type_of = (uu___89_6189.check_type_of);
        use_bv_sorts = (uu___89_6189.use_bv_sorts);
        qtbl_name_and_index = (uu___89_6189.qtbl_name_and_index);
        proof_ns = (uu___89_6189.proof_ns);
        synth = (uu___89_6189.synth);
        splice = (uu___89_6189.splice);
        is_native_tactic = (uu___89_6189.is_native_tactic);
        identifier_info = (uu___89_6189.identifier_info);
        tc_hooks = (uu___89_6189.tc_hooks);
        dsenv = (uu___89_6189.dsenv);
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
      | (NoDelta ,uu____6204) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____6205,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____6206,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____6207 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____6214 . Prims.unit -> 'Auu____6214 FStar_Util.smap =
  fun uu____6220  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____6223 . Prims.unit -> 'Auu____6223 FStar_Util.smap =
  fun uu____6229  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____6325 = new_gamma_cache ()  in
                let uu____6328 = new_sigtab ()  in
                let uu____6331 =
                  let uu____6344 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____6344, FStar_Pervasives_Native.None)  in
                let uu____6359 = FStar_Options.using_facts_from ()  in
                let uu____6360 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____6363 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____6325;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____6328;
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
                  qtbl_name_and_index = uu____6331;
                  proof_ns = uu____6359;
                  synth =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____6399  -> false);
                  identifier_info = uu____6360;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____6363;
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
  fun uu____6482  ->
    let uu____6483 = FStar_ST.op_Bang query_indices  in
    match uu____6483 with
    | [] -> failwith "Empty query indices!"
    | uu____6533 ->
        let uu____6542 =
          let uu____6551 =
            let uu____6558 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____6558  in
          let uu____6608 = FStar_ST.op_Bang query_indices  in uu____6551 ::
            uu____6608
           in
        FStar_ST.op_Colon_Equals query_indices uu____6542
  
let (pop_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6695  ->
    let uu____6696 = FStar_ST.op_Bang query_indices  in
    match uu____6696 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____6809  ->
    match uu____6809 with
    | (l,n1) ->
        let uu____6816 = FStar_ST.op_Bang query_indices  in
        (match uu____6816 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6927 -> failwith "Empty query indices")
  
let (peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6944  ->
    let uu____6945 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6945
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____7016 =
       let uu____7019 = FStar_ST.op_Bang stack  in env :: uu____7019  in
     FStar_ST.op_Colon_Equals stack uu____7016);
    (let uu___90_7068 = env  in
     let uu____7069 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____7072 = FStar_Util.smap_copy (sigtab env)  in
     let uu____7075 =
       let uu____7088 =
         let uu____7091 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____7091  in
       let uu____7116 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____7088, uu____7116)  in
     let uu____7157 =
       let uu____7160 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____7160  in
     {
       solver = (uu___90_7068.solver);
       range = (uu___90_7068.range);
       curmodule = (uu___90_7068.curmodule);
       gamma = (uu___90_7068.gamma);
       gamma_cache = uu____7069;
       modules = (uu___90_7068.modules);
       expected_typ = (uu___90_7068.expected_typ);
       sigtab = uu____7072;
       is_pattern = (uu___90_7068.is_pattern);
       instantiate_imp = (uu___90_7068.instantiate_imp);
       effects = (uu___90_7068.effects);
       generalize = (uu___90_7068.generalize);
       letrecs = (uu___90_7068.letrecs);
       top_level = (uu___90_7068.top_level);
       check_uvars = (uu___90_7068.check_uvars);
       use_eq = (uu___90_7068.use_eq);
       is_iface = (uu___90_7068.is_iface);
       admit = (uu___90_7068.admit);
       lax = (uu___90_7068.lax);
       lax_universes = (uu___90_7068.lax_universes);
       failhard = (uu___90_7068.failhard);
       nosynth = (uu___90_7068.nosynth);
       tc_term = (uu___90_7068.tc_term);
       type_of = (uu___90_7068.type_of);
       universe_of = (uu___90_7068.universe_of);
       check_type_of = (uu___90_7068.check_type_of);
       use_bv_sorts = (uu___90_7068.use_bv_sorts);
       qtbl_name_and_index = uu____7075;
       proof_ns = (uu___90_7068.proof_ns);
       synth = (uu___90_7068.synth);
       splice = (uu___90_7068.splice);
       is_native_tactic = (uu___90_7068.is_native_tactic);
       identifier_info = uu____7157;
       tc_hooks = (uu___90_7068.tc_hooks);
       dsenv = (uu___90_7068.dsenv);
       dep_graph = (uu___90_7068.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____7204  ->
    let uu____7205 = FStar_ST.op_Bang stack  in
    match uu____7205 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____7259 -> failwith "Impossible: Too many pops"
  
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
    | (uu____7288,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____7320 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____7346  ->
                  match uu____7346 with
                  | (m,uu____7352) -> FStar_Ident.lid_equals l m))
           in
        (match uu____7320 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___91_7360 = env  in
               {
                 solver = (uu___91_7360.solver);
                 range = (uu___91_7360.range);
                 curmodule = (uu___91_7360.curmodule);
                 gamma = (uu___91_7360.gamma);
                 gamma_cache = (uu___91_7360.gamma_cache);
                 modules = (uu___91_7360.modules);
                 expected_typ = (uu___91_7360.expected_typ);
                 sigtab = (uu___91_7360.sigtab);
                 is_pattern = (uu___91_7360.is_pattern);
                 instantiate_imp = (uu___91_7360.instantiate_imp);
                 effects = (uu___91_7360.effects);
                 generalize = (uu___91_7360.generalize);
                 letrecs = (uu___91_7360.letrecs);
                 top_level = (uu___91_7360.top_level);
                 check_uvars = (uu___91_7360.check_uvars);
                 use_eq = (uu___91_7360.use_eq);
                 is_iface = (uu___91_7360.is_iface);
                 admit = (uu___91_7360.admit);
                 lax = (uu___91_7360.lax);
                 lax_universes = (uu___91_7360.lax_universes);
                 failhard = (uu___91_7360.failhard);
                 nosynth = (uu___91_7360.nosynth);
                 tc_term = (uu___91_7360.tc_term);
                 type_of = (uu___91_7360.type_of);
                 universe_of = (uu___91_7360.universe_of);
                 check_type_of = (uu___91_7360.check_type_of);
                 use_bv_sorts = (uu___91_7360.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___91_7360.proof_ns);
                 synth = (uu___91_7360.synth);
                 splice = (uu___91_7360.splice);
                 is_native_tactic = (uu___91_7360.is_native_tactic);
                 identifier_info = (uu___91_7360.identifier_info);
                 tc_hooks = (uu___91_7360.tc_hooks);
                 dsenv = (uu___91_7360.dsenv);
                 dep_graph = (uu___91_7360.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____7373,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___92_7382 = env  in
               {
                 solver = (uu___92_7382.solver);
                 range = (uu___92_7382.range);
                 curmodule = (uu___92_7382.curmodule);
                 gamma = (uu___92_7382.gamma);
                 gamma_cache = (uu___92_7382.gamma_cache);
                 modules = (uu___92_7382.modules);
                 expected_typ = (uu___92_7382.expected_typ);
                 sigtab = (uu___92_7382.sigtab);
                 is_pattern = (uu___92_7382.is_pattern);
                 instantiate_imp = (uu___92_7382.instantiate_imp);
                 effects = (uu___92_7382.effects);
                 generalize = (uu___92_7382.generalize);
                 letrecs = (uu___92_7382.letrecs);
                 top_level = (uu___92_7382.top_level);
                 check_uvars = (uu___92_7382.check_uvars);
                 use_eq = (uu___92_7382.use_eq);
                 is_iface = (uu___92_7382.is_iface);
                 admit = (uu___92_7382.admit);
                 lax = (uu___92_7382.lax);
                 lax_universes = (uu___92_7382.lax_universes);
                 failhard = (uu___92_7382.failhard);
                 nosynth = (uu___92_7382.nosynth);
                 tc_term = (uu___92_7382.tc_term);
                 type_of = (uu___92_7382.type_of);
                 universe_of = (uu___92_7382.universe_of);
                 check_type_of = (uu___92_7382.check_type_of);
                 use_bv_sorts = (uu___92_7382.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___92_7382.proof_ns);
                 synth = (uu___92_7382.synth);
                 splice = (uu___92_7382.splice);
                 is_native_tactic = (uu___92_7382.is_native_tactic);
                 identifier_info = (uu___92_7382.identifier_info);
                 tc_hooks = (uu___92_7382.tc_hooks);
                 dsenv = (uu___92_7382.dsenv);
                 dep_graph = (uu___92_7382.dep_graph)
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
        (let uu___93_7408 = e  in
         {
           solver = (uu___93_7408.solver);
           range = r;
           curmodule = (uu___93_7408.curmodule);
           gamma = (uu___93_7408.gamma);
           gamma_cache = (uu___93_7408.gamma_cache);
           modules = (uu___93_7408.modules);
           expected_typ = (uu___93_7408.expected_typ);
           sigtab = (uu___93_7408.sigtab);
           is_pattern = (uu___93_7408.is_pattern);
           instantiate_imp = (uu___93_7408.instantiate_imp);
           effects = (uu___93_7408.effects);
           generalize = (uu___93_7408.generalize);
           letrecs = (uu___93_7408.letrecs);
           top_level = (uu___93_7408.top_level);
           check_uvars = (uu___93_7408.check_uvars);
           use_eq = (uu___93_7408.use_eq);
           is_iface = (uu___93_7408.is_iface);
           admit = (uu___93_7408.admit);
           lax = (uu___93_7408.lax);
           lax_universes = (uu___93_7408.lax_universes);
           failhard = (uu___93_7408.failhard);
           nosynth = (uu___93_7408.nosynth);
           tc_term = (uu___93_7408.tc_term);
           type_of = (uu___93_7408.type_of);
           universe_of = (uu___93_7408.universe_of);
           check_type_of = (uu___93_7408.check_type_of);
           use_bv_sorts = (uu___93_7408.use_bv_sorts);
           qtbl_name_and_index = (uu___93_7408.qtbl_name_and_index);
           proof_ns = (uu___93_7408.proof_ns);
           synth = (uu___93_7408.synth);
           splice = (uu___93_7408.splice);
           is_native_tactic = (uu___93_7408.is_native_tactic);
           identifier_info = (uu___93_7408.identifier_info);
           tc_hooks = (uu___93_7408.tc_hooks);
           dsenv = (uu___93_7408.dsenv);
           dep_graph = (uu___93_7408.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____7418 =
        let uu____7419 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____7419 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7418
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____7467 =
          let uu____7468 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____7468 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7467
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____7516 =
          let uu____7517 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____7517 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7516
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____7567 =
        let uu____7568 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____7568 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7567
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___94_7621 = env  in
      {
        solver = (uu___94_7621.solver);
        range = (uu___94_7621.range);
        curmodule = lid;
        gamma = (uu___94_7621.gamma);
        gamma_cache = (uu___94_7621.gamma_cache);
        modules = (uu___94_7621.modules);
        expected_typ = (uu___94_7621.expected_typ);
        sigtab = (uu___94_7621.sigtab);
        is_pattern = (uu___94_7621.is_pattern);
        instantiate_imp = (uu___94_7621.instantiate_imp);
        effects = (uu___94_7621.effects);
        generalize = (uu___94_7621.generalize);
        letrecs = (uu___94_7621.letrecs);
        top_level = (uu___94_7621.top_level);
        check_uvars = (uu___94_7621.check_uvars);
        use_eq = (uu___94_7621.use_eq);
        is_iface = (uu___94_7621.is_iface);
        admit = (uu___94_7621.admit);
        lax = (uu___94_7621.lax);
        lax_universes = (uu___94_7621.lax_universes);
        failhard = (uu___94_7621.failhard);
        nosynth = (uu___94_7621.nosynth);
        tc_term = (uu___94_7621.tc_term);
        type_of = (uu___94_7621.type_of);
        universe_of = (uu___94_7621.universe_of);
        check_type_of = (uu___94_7621.check_type_of);
        use_bv_sorts = (uu___94_7621.use_bv_sorts);
        qtbl_name_and_index = (uu___94_7621.qtbl_name_and_index);
        proof_ns = (uu___94_7621.proof_ns);
        synth = (uu___94_7621.synth);
        splice = (uu___94_7621.splice);
        is_native_tactic = (uu___94_7621.is_native_tactic);
        identifier_info = (uu___94_7621.identifier_info);
        tc_hooks = (uu___94_7621.tc_hooks);
        dsenv = (uu___94_7621.dsenv);
        dep_graph = (uu___94_7621.dep_graph)
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
    let uu____7647 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7647)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____7655 =
      let uu____7656 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7656  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7655)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____7659  ->
    let uu____7660 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7660
  
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
      | ((formals,t),uu____7698) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7722 = FStar_Syntax_Subst.subst vs t  in (us, uu____7722)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___72_7735  ->
    match uu___72_7735 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7759  -> new_u_univ ()))
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
      let uu____7772 = inst_tscheme t  in
      match uu____7772 with
      | (us,t1) ->
          let uu____7783 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7783)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7795  ->
          match uu____7795 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7810 =
                         let uu____7811 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7812 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7813 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7814 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7811 uu____7812 uu____7813 uu____7814
                          in
                       failwith uu____7810)
                    else ();
                    (let uu____7816 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7816))
               | uu____7823 ->
                   let uu____7824 =
                     let uu____7825 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7825
                      in
                   failwith uu____7824)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____7829 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____7833 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7837 -> false
  
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
             | ([],uu____7871) -> Maybe
             | (uu____7878,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7897 -> No  in
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
          let uu____7982 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7982 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___73_8027  ->
                   match uu___73_8027 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____8070 =
                           let uu____8089 =
                             let uu____8104 = inst_tscheme t  in
                             FStar_Util.Inl uu____8104  in
                           (uu____8089, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____8070
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____8170,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____8172);
                                     FStar_Syntax_Syntax.sigrng = uu____8173;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____8174;
                                     FStar_Syntax_Syntax.sigmeta = uu____8175;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____8176;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____8196 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____8196
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____8242 ->
                             FStar_Pervasives_Native.Some t
                         | uu____8249 -> cache t  in
                       let uu____8250 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____8250 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____8325 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____8325 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____8411 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____8471 = find_in_sigtab env lid  in
         match uu____8471 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8550) ->
          add_sigelts env ses
      | uu____8559 ->
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
            | uu____8573 -> ()))

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
        (fun uu___74_8600  ->
           match uu___74_8600 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8618 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____8671,lb::[]),uu____8673) ->
            let uu____8686 =
              let uu____8695 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____8704 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____8695, uu____8704)  in
            FStar_Pervasives_Native.Some uu____8686
        | FStar_Syntax_Syntax.Sig_let ((uu____8717,lbs),uu____8719) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____8755 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____8767 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____8767
                     then
                       let uu____8778 =
                         let uu____8787 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____8796 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____8787, uu____8796)  in
                       FStar_Pervasives_Native.Some uu____8778
                     else FStar_Pervasives_Native.None)
        | uu____8818 -> FStar_Pervasives_Native.None
  
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
          let uu____8871 =
            let uu____8880 =
              let uu____8885 =
                let uu____8886 =
                  let uu____8889 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____8889
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____8886)  in
              inst_tscheme1 uu____8885  in
            (uu____8880, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8871
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____8909,uu____8910) ->
          let uu____8915 =
            let uu____8924 =
              let uu____8929 =
                let uu____8930 =
                  let uu____8933 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____8933  in
                (us, uu____8930)  in
              inst_tscheme1 uu____8929  in
            (uu____8924, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8915
      | uu____8950 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____9028 =
          match uu____9028 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____9124,uvs,t,uu____9127,uu____9128,uu____9129);
                      FStar_Syntax_Syntax.sigrng = uu____9130;
                      FStar_Syntax_Syntax.sigquals = uu____9131;
                      FStar_Syntax_Syntax.sigmeta = uu____9132;
                      FStar_Syntax_Syntax.sigattrs = uu____9133;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____9154 =
                     let uu____9163 = inst_tscheme1 (uvs, t)  in
                     (uu____9163, rng)  in
                   FStar_Pervasives_Native.Some uu____9154
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____9183;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____9185;
                      FStar_Syntax_Syntax.sigattrs = uu____9186;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____9203 =
                     let uu____9204 = in_cur_mod env l  in uu____9204 = Yes
                      in
                   if uu____9203
                   then
                     let uu____9215 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____9215
                      then
                        let uu____9228 =
                          let uu____9237 = inst_tscheme1 (uvs, t)  in
                          (uu____9237, rng)  in
                        FStar_Pervasives_Native.Some uu____9228
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9264 =
                        let uu____9273 = inst_tscheme1 (uvs, t)  in
                        (uu____9273, rng)  in
                      FStar_Pervasives_Native.Some uu____9264)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9294,uu____9295);
                      FStar_Syntax_Syntax.sigrng = uu____9296;
                      FStar_Syntax_Syntax.sigquals = uu____9297;
                      FStar_Syntax_Syntax.sigmeta = uu____9298;
                      FStar_Syntax_Syntax.sigattrs = uu____9299;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____9338 =
                          let uu____9347 = inst_tscheme1 (uvs, k)  in
                          (uu____9347, rng)  in
                        FStar_Pervasives_Native.Some uu____9338
                    | uu____9364 ->
                        let uu____9365 =
                          let uu____9374 =
                            let uu____9379 =
                              let uu____9380 =
                                let uu____9383 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9383
                                 in
                              (uvs, uu____9380)  in
                            inst_tscheme1 uu____9379  in
                          (uu____9374, rng)  in
                        FStar_Pervasives_Native.Some uu____9365)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9404,uu____9405);
                      FStar_Syntax_Syntax.sigrng = uu____9406;
                      FStar_Syntax_Syntax.sigquals = uu____9407;
                      FStar_Syntax_Syntax.sigmeta = uu____9408;
                      FStar_Syntax_Syntax.sigattrs = uu____9409;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____9449 =
                          let uu____9458 = inst_tscheme_with (uvs, k) us  in
                          (uu____9458, rng)  in
                        FStar_Pervasives_Native.Some uu____9449
                    | uu____9475 ->
                        let uu____9476 =
                          let uu____9485 =
                            let uu____9490 =
                              let uu____9491 =
                                let uu____9494 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9494
                                 in
                              (uvs, uu____9491)  in
                            inst_tscheme_with uu____9490 us  in
                          (uu____9485, rng)  in
                        FStar_Pervasives_Native.Some uu____9476)
               | FStar_Util.Inr se ->
                   let uu____9528 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____9549;
                          FStar_Syntax_Syntax.sigrng = uu____9550;
                          FStar_Syntax_Syntax.sigquals = uu____9551;
                          FStar_Syntax_Syntax.sigmeta = uu____9552;
                          FStar_Syntax_Syntax.sigattrs = uu____9553;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____9568 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____9528
                     (FStar_Util.map_option
                        (fun uu____9616  ->
                           match uu____9616 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____9647 =
          let uu____9658 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____9658 mapper  in
        match uu____9647 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            FStar_Pervasives_Native.Some
              ((us,
                 (let uu___95_9751 = t  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___95_9751.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                    FStar_Syntax_Syntax.vars =
                      (uu___95_9751.FStar_Syntax_Syntax.vars)
                  })), r)
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____9776 = lookup_qname env l  in
      match uu____9776 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9795 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9843 = try_lookup_bv env bv  in
      match uu____9843 with
      | FStar_Pervasives_Native.None  ->
          let uu____9858 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9858 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9873 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9874 =
            let uu____9875 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9875  in
          (uu____9873, uu____9874)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____9892 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____9892 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9958 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9958  in
          let uu____9959 =
            let uu____9968 =
              let uu____9973 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9973)  in
            (uu____9968, r1)  in
          FStar_Pervasives_Native.Some uu____9959
  
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
        let uu____10001 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____10001 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____10034,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____10059 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____10059  in
            let uu____10060 =
              let uu____10065 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____10065, r1)  in
            FStar_Pervasives_Native.Some uu____10060
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____10084 = try_lookup_lid env l  in
      match uu____10084 with
      | FStar_Pervasives_Native.None  ->
          let uu____10111 = name_not_found l  in
          FStar_Errors.raise_error uu____10111 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___75_10151  ->
              match uu___75_10151 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____10153 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10168 = lookup_qname env lid  in
      match uu____10168 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10177,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____10180;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10182;
              FStar_Syntax_Syntax.sigattrs = uu____10183;_},FStar_Pervasives_Native.None
            ),uu____10184)
          ->
          let uu____10233 =
            let uu____10244 =
              let uu____10249 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____10249)  in
            (uu____10244, q)  in
          FStar_Pervasives_Native.Some uu____10233
      | uu____10266 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10283 = lookup_qname env lid  in
      match uu____10283 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10288,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____10291;
              FStar_Syntax_Syntax.sigquals = uu____10292;
              FStar_Syntax_Syntax.sigmeta = uu____10293;
              FStar_Syntax_Syntax.sigattrs = uu____10294;_},FStar_Pervasives_Native.None
            ),uu____10295)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____10344 ->
          let uu____10345 = name_not_found lid  in
          FStar_Errors.raise_error uu____10345 (FStar_Ident.range_of_lid lid)
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10364 = lookup_qname env lid  in
      match uu____10364 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10369,uvs,t,uu____10372,uu____10373,uu____10374);
              FStar_Syntax_Syntax.sigrng = uu____10375;
              FStar_Syntax_Syntax.sigquals = uu____10376;
              FStar_Syntax_Syntax.sigmeta = uu____10377;
              FStar_Syntax_Syntax.sigattrs = uu____10378;_},FStar_Pervasives_Native.None
            ),uu____10379)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____10432 ->
          let uu____10433 = name_not_found lid  in
          FStar_Errors.raise_error uu____10433 (FStar_Ident.range_of_lid lid)
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10454 = lookup_qname env lid  in
      match uu____10454 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10461,uu____10462,uu____10463,uu____10464,uu____10465,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10467;
              FStar_Syntax_Syntax.sigquals = uu____10468;
              FStar_Syntax_Syntax.sigmeta = uu____10469;
              FStar_Syntax_Syntax.sigattrs = uu____10470;_},uu____10471),uu____10472)
          -> (true, dcs)
      | uu____10533 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____10542 = lookup_qname env lid  in
      match uu____10542 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10543,uu____10544,uu____10545,l,uu____10547,uu____10548);
              FStar_Syntax_Syntax.sigrng = uu____10549;
              FStar_Syntax_Syntax.sigquals = uu____10550;
              FStar_Syntax_Syntax.sigmeta = uu____10551;
              FStar_Syntax_Syntax.sigattrs = uu____10552;_},uu____10553),uu____10554)
          -> l
      | uu____10609 ->
          let uu____10610 =
            let uu____10611 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10611  in
          failwith uu____10610
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10652)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10703,lbs),uu____10705)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10733 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10733
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10765 -> FStar_Pervasives_Native.None)
        | uu____10770 -> FStar_Pervasives_Native.None
  
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
        let uu____10794 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____10794
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____10817),uu____10818) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____10867 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10884 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____10884
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____10899 = lookup_qname env ftv  in
      match uu____10899 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10903) ->
          let uu____10948 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____10948 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10969,t),r) ->
               let uu____10984 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10984)
      | uu____10985 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____10992 = try_lookup_effect_lid env ftv  in
      match uu____10992 with
      | FStar_Pervasives_Native.None  ->
          let uu____10995 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10995 (FStar_Ident.range_of_lid ftv)
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
        let uu____11016 = lookup_qname env lid0  in
        match uu____11016 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____11027);
                FStar_Syntax_Syntax.sigrng = uu____11028;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____11030;
                FStar_Syntax_Syntax.sigattrs = uu____11031;_},FStar_Pervasives_Native.None
              ),uu____11032)
            ->
            let lid1 =
              let uu____11086 =
                let uu____11087 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____11087
                 in
              FStar_Ident.set_lid_range lid uu____11086  in
            let uu____11088 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___76_11092  ->
                      match uu___76_11092 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11093 -> false))
               in
            if uu____11088
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____11107 =
                      let uu____11108 =
                        let uu____11109 = get_range env  in
                        FStar_Range.string_of_range uu____11109  in
                      let uu____11110 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____11111 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____11108 uu____11110 uu____11111
                       in
                    failwith uu____11107)
                  in
               match (binders, univs1) with
               | ([],uu____11118) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____11135,uu____11136::uu____11137::uu____11138) ->
                   let uu____11143 =
                     let uu____11144 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____11145 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____11144 uu____11145
                      in
                   failwith uu____11143
               | uu____11152 ->
                   let uu____11157 =
                     let uu____11162 =
                       let uu____11163 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____11163)  in
                     inst_tscheme_with uu____11162 insts  in
                   (match uu____11157 with
                    | (uu____11174,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____11177 =
                          let uu____11178 = FStar_Syntax_Subst.compress t1
                             in
                          uu____11178.FStar_Syntax_Syntax.n  in
                        (match uu____11177 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____11225 -> failwith "Impossible")))
        | uu____11232 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____11252 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____11252 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____11265,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____11272 = find1 l2  in
            (match uu____11272 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____11279 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____11279 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____11283 = find1 l  in
            (match uu____11283 with
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
      let uu____11297 = lookup_qname env l1  in
      match uu____11297 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____11300;
              FStar_Syntax_Syntax.sigrng = uu____11301;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11303;
              FStar_Syntax_Syntax.sigattrs = uu____11304;_},uu____11305),uu____11306)
          -> q
      | uu____11357 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____11370 =
          let uu____11371 =
            let uu____11372 = FStar_Util.string_of_int i  in
            let uu____11373 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____11372 uu____11373
             in
          failwith uu____11371  in
        let uu____11374 = lookup_datacon env lid  in
        match uu____11374 with
        | (uu____11379,t) ->
            let uu____11381 =
              let uu____11382 = FStar_Syntax_Subst.compress t  in
              uu____11382.FStar_Syntax_Syntax.n  in
            (match uu____11381 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11386) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____11417 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____11417
                      FStar_Pervasives_Native.fst)
             | uu____11426 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11433 = lookup_qname env l  in
      match uu____11433 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11434,uu____11435,uu____11436);
              FStar_Syntax_Syntax.sigrng = uu____11437;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11439;
              FStar_Syntax_Syntax.sigattrs = uu____11440;_},uu____11441),uu____11442)
          ->
          FStar_Util.for_some
            (fun uu___77_11495  ->
               match uu___77_11495 with
               | FStar_Syntax_Syntax.Projector uu____11496 -> true
               | uu____11501 -> false) quals
      | uu____11502 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11509 = lookup_qname env lid  in
      match uu____11509 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11510,uu____11511,uu____11512,uu____11513,uu____11514,uu____11515);
              FStar_Syntax_Syntax.sigrng = uu____11516;
              FStar_Syntax_Syntax.sigquals = uu____11517;
              FStar_Syntax_Syntax.sigmeta = uu____11518;
              FStar_Syntax_Syntax.sigattrs = uu____11519;_},uu____11520),uu____11521)
          -> true
      | uu____11576 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11583 = lookup_qname env lid  in
      match uu____11583 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11584,uu____11585,uu____11586,uu____11587,uu____11588,uu____11589);
              FStar_Syntax_Syntax.sigrng = uu____11590;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11592;
              FStar_Syntax_Syntax.sigattrs = uu____11593;_},uu____11594),uu____11595)
          ->
          FStar_Util.for_some
            (fun uu___78_11656  ->
               match uu___78_11656 with
               | FStar_Syntax_Syntax.RecordType uu____11657 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11666 -> true
               | uu____11675 -> false) quals
      | uu____11676 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____11680,uu____11681);
            FStar_Syntax_Syntax.sigrng = uu____11682;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____11684;
            FStar_Syntax_Syntax.sigattrs = uu____11685;_},uu____11686),uu____11687)
        ->
        FStar_Util.for_some
          (fun uu___79_11744  ->
             match uu___79_11744 with
             | FStar_Syntax_Syntax.Action uu____11745 -> true
             | uu____11746 -> false) quals
    | uu____11747 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11754 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____11754
  
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
      let uu____11764 =
        let uu____11765 = FStar_Syntax_Util.un_uinst head1  in
        uu____11765.FStar_Syntax_Syntax.n  in
      match uu____11764 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11769 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11776 = lookup_qname env l  in
      match uu____11776 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11778),uu____11779) ->
          FStar_Util.for_some
            (fun uu___80_11827  ->
               match uu___80_11827 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11828 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11829 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11894 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11910) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11927 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11934 ->
                 FStar_Pervasives_Native.Some true
             | uu____11951 -> FStar_Pervasives_Native.Some false)
         in
      let uu____11952 =
        let uu____11955 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____11955 mapper  in
      match uu____11952 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____12001 = lookup_qname env lid  in
      match uu____12001 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12002,uu____12003,tps,uu____12005,uu____12006,uu____12007);
              FStar_Syntax_Syntax.sigrng = uu____12008;
              FStar_Syntax_Syntax.sigquals = uu____12009;
              FStar_Syntax_Syntax.sigmeta = uu____12010;
              FStar_Syntax_Syntax.sigattrs = uu____12011;_},uu____12012),uu____12013)
          -> FStar_List.length tps
      | uu____12076 ->
          let uu____12077 = name_not_found lid  in
          FStar_Errors.raise_error uu____12077 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____12121  ->
              match uu____12121 with
              | (d,uu____12129) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____12140 = effect_decl_opt env l  in
      match uu____12140 with
      | FStar_Pervasives_Native.None  ->
          let uu____12155 = name_not_found l  in
          FStar_Errors.raise_error uu____12155 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____12181  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____12196  ->
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
            (let uu____12229 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____12282  ->
                       match uu____12282 with
                       | (m1,m2,uu____12295,uu____12296,uu____12297) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____12229 with
             | FStar_Pervasives_Native.None  ->
                 let uu____12314 =
                   let uu____12319 =
                     let uu____12320 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____12321 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____12320
                       uu____12321
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____12319)
                    in
                 FStar_Errors.raise_error uu____12314 env.range
             | FStar_Pervasives_Native.Some
                 (uu____12328,uu____12329,m3,j1,j2) -> (m3, j1, j2))
  
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
  'Auu____12366 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12366)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12393 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12419  ->
                match uu____12419 with
                | (d,uu____12425) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____12393 with
      | FStar_Pervasives_Native.None  ->
          let uu____12436 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12436
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12449 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12449 with
           | (uu____12460,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12470)::(wp,uu____12472)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12508 -> failwith "Impossible"))
  
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
                 let uu____12551 = get_range env  in
                 let uu____12552 =
                   let uu____12555 =
                     let uu____12556 =
                       let uu____12571 =
                         let uu____12574 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____12574]  in
                       (null_wp, uu____12571)  in
                     FStar_Syntax_Syntax.Tm_app uu____12556  in
                   FStar_Syntax_Syntax.mk uu____12555  in
                 uu____12552 FStar_Pervasives_Native.None uu____12551  in
               let uu____12580 =
                 let uu____12581 =
                   let uu____12590 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____12590]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12581;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____12580)
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___96_12599 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___96_12599.order);
              joins = (uu___96_12599.joins)
            }  in
          let uu___97_12608 = env  in
          {
            solver = (uu___97_12608.solver);
            range = (uu___97_12608.range);
            curmodule = (uu___97_12608.curmodule);
            gamma = (uu___97_12608.gamma);
            gamma_cache = (uu___97_12608.gamma_cache);
            modules = (uu___97_12608.modules);
            expected_typ = (uu___97_12608.expected_typ);
            sigtab = (uu___97_12608.sigtab);
            is_pattern = (uu___97_12608.is_pattern);
            instantiate_imp = (uu___97_12608.instantiate_imp);
            effects;
            generalize = (uu___97_12608.generalize);
            letrecs = (uu___97_12608.letrecs);
            top_level = (uu___97_12608.top_level);
            check_uvars = (uu___97_12608.check_uvars);
            use_eq = (uu___97_12608.use_eq);
            is_iface = (uu___97_12608.is_iface);
            admit = (uu___97_12608.admit);
            lax = (uu___97_12608.lax);
            lax_universes = (uu___97_12608.lax_universes);
            failhard = (uu___97_12608.failhard);
            nosynth = (uu___97_12608.nosynth);
            tc_term = (uu___97_12608.tc_term);
            type_of = (uu___97_12608.type_of);
            universe_of = (uu___97_12608.universe_of);
            check_type_of = (uu___97_12608.check_type_of);
            use_bv_sorts = (uu___97_12608.use_bv_sorts);
            qtbl_name_and_index = (uu___97_12608.qtbl_name_and_index);
            proof_ns = (uu___97_12608.proof_ns);
            synth = (uu___97_12608.synth);
            splice = (uu___97_12608.splice);
            is_native_tactic = (uu___97_12608.is_native_tactic);
            identifier_info = (uu___97_12608.identifier_info);
            tc_hooks = (uu___97_12608.tc_hooks);
            dsenv = (uu___97_12608.dsenv);
            dep_graph = (uu___97_12608.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12628 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12628  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12742 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12743 = l1 u t wp e  in
                                l2 u t uu____12742 uu____12743))
                | uu____12744 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12792 = inst_tscheme_with lift_t [u]  in
            match uu____12792 with
            | (uu____12799,lift_t1) ->
                let uu____12801 =
                  let uu____12804 =
                    let uu____12805 =
                      let uu____12820 =
                        let uu____12823 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12824 =
                          let uu____12827 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12827]  in
                        uu____12823 :: uu____12824  in
                      (lift_t1, uu____12820)  in
                    FStar_Syntax_Syntax.Tm_app uu____12805  in
                  FStar_Syntax_Syntax.mk uu____12804  in
                uu____12801 FStar_Pervasives_Native.None
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
            let uu____12877 = inst_tscheme_with lift_t [u]  in
            match uu____12877 with
            | (uu____12884,lift_t1) ->
                let uu____12886 =
                  let uu____12889 =
                    let uu____12890 =
                      let uu____12905 =
                        let uu____12908 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12909 =
                          let uu____12912 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12913 =
                            let uu____12916 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12916]  in
                          uu____12912 :: uu____12913  in
                        uu____12908 :: uu____12909  in
                      (lift_t1, uu____12905)  in
                    FStar_Syntax_Syntax.Tm_app uu____12890  in
                  FStar_Syntax_Syntax.mk uu____12889  in
                uu____12886 FStar_Pervasives_Native.None
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
              let uu____12958 =
                let uu____12959 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____12959
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____12958  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____12963 =
              let uu____12964 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____12964  in
            let uu____12965 =
              let uu____12966 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12988 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____12988)
                 in
              FStar_Util.dflt "none" uu____12966  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12963
              uu____12965
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____13014  ->
                    match uu____13014 with
                    | (e,uu____13022) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____13041 =
            match uu____13041 with
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
              let uu____13079 =
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
                                    (let uu____13100 =
                                       let uu____13109 =
                                         find_edge order1 (i, k)  in
                                       let uu____13112 =
                                         find_edge order1 (k, j)  in
                                       (uu____13109, uu____13112)  in
                                     match uu____13100 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____13127 =
                                           compose_edges e1 e2  in
                                         [uu____13127]
                                     | uu____13128 -> [])))))
                 in
              FStar_List.append order1 uu____13079  in
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
                   let uu____13158 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____13160 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____13160
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____13158
                   then
                     let uu____13165 =
                       let uu____13170 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____13170)
                        in
                     let uu____13171 = get_range env  in
                     FStar_Errors.raise_error uu____13165 uu____13171
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
                                            let uu____13296 =
                                              let uu____13305 =
                                                find_edge order2 (i, k)  in
                                              let uu____13308 =
                                                find_edge order2 (j, k)  in
                                              (uu____13305, uu____13308)  in
                                            match uu____13296 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13350,uu____13351)
                                                     ->
                                                     let uu____13358 =
                                                       let uu____13363 =
                                                         let uu____13364 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13364
                                                          in
                                                       let uu____13367 =
                                                         let uu____13368 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13368
                                                          in
                                                       (uu____13363,
                                                         uu____13367)
                                                        in
                                                     (match uu____13358 with
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
                                            | uu____13403 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___98_13476 = env.effects  in
              { decls = (uu___98_13476.decls); order = order2; joins }  in
            let uu___99_13477 = env  in
            {
              solver = (uu___99_13477.solver);
              range = (uu___99_13477.range);
              curmodule = (uu___99_13477.curmodule);
              gamma = (uu___99_13477.gamma);
              gamma_cache = (uu___99_13477.gamma_cache);
              modules = (uu___99_13477.modules);
              expected_typ = (uu___99_13477.expected_typ);
              sigtab = (uu___99_13477.sigtab);
              is_pattern = (uu___99_13477.is_pattern);
              instantiate_imp = (uu___99_13477.instantiate_imp);
              effects;
              generalize = (uu___99_13477.generalize);
              letrecs = (uu___99_13477.letrecs);
              top_level = (uu___99_13477.top_level);
              check_uvars = (uu___99_13477.check_uvars);
              use_eq = (uu___99_13477.use_eq);
              is_iface = (uu___99_13477.is_iface);
              admit = (uu___99_13477.admit);
              lax = (uu___99_13477.lax);
              lax_universes = (uu___99_13477.lax_universes);
              failhard = (uu___99_13477.failhard);
              nosynth = (uu___99_13477.nosynth);
              tc_term = (uu___99_13477.tc_term);
              type_of = (uu___99_13477.type_of);
              universe_of = (uu___99_13477.universe_of);
              check_type_of = (uu___99_13477.check_type_of);
              use_bv_sorts = (uu___99_13477.use_bv_sorts);
              qtbl_name_and_index = (uu___99_13477.qtbl_name_and_index);
              proof_ns = (uu___99_13477.proof_ns);
              synth = (uu___99_13477.synth);
              splice = (uu___99_13477.splice);
              is_native_tactic = (uu___99_13477.is_native_tactic);
              identifier_info = (uu___99_13477.identifier_info);
              tc_hooks = (uu___99_13477.tc_hooks);
              dsenv = (uu___99_13477.dsenv);
              dep_graph = (uu___99_13477.dep_graph)
            }))
      | uu____13478 -> env
  
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
        | uu____13502 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13510 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13510 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13527 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13527 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13545 =
                     let uu____13550 =
                       let uu____13551 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13556 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13563 =
                         let uu____13564 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13564  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13551 uu____13556 uu____13563
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13550)
                      in
                   FStar_Errors.raise_error uu____13545
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13569 =
                     let uu____13578 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13578 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13595  ->
                        fun uu____13596  ->
                          match (uu____13595, uu____13596) with
                          | ((x,uu____13618),(t,uu____13620)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13569
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13639 =
                     let uu___100_13640 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___100_13640.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___100_13640.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___100_13640.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___100_13640.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13639
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
          let uu____13662 = effect_decl_opt env effect_name  in
          match uu____13662 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13695 =
                only_reifiable &&
                  (let uu____13697 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13697)
                 in
              if uu____13695
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13713 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13732 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13761 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13761
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13762 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13762
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13772 =
                       let uu____13775 = get_range env  in
                       let uu____13776 =
                         let uu____13779 =
                           let uu____13780 =
                             let uu____13795 =
                               let uu____13798 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13798; wp]  in
                             (repr, uu____13795)  in
                           FStar_Syntax_Syntax.Tm_app uu____13780  in
                         FStar_Syntax_Syntax.mk uu____13779  in
                       uu____13776 FStar_Pervasives_Native.None uu____13775
                        in
                     FStar_Pervasives_Native.Some uu____13772)
  
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
          let uu____13844 =
            let uu____13849 =
              let uu____13850 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13850
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13849)  in
          let uu____13851 = get_range env  in
          FStar_Errors.raise_error uu____13844 uu____13851  in
        let uu____13852 = effect_repr_aux true env c u_c  in
        match uu____13852 with
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
      | uu____13886 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____13893 =
        let uu____13894 = FStar_Syntax_Subst.compress t  in
        uu____13894.FStar_Syntax_Syntax.n  in
      match uu____13893 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13897,c) ->
          is_reifiable_comp env c
      | uu____13915 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13937)::uu____13938 -> x :: rest
        | (Binding_sig_inst uu____13947)::uu____13948 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13963 = push1 x rest1  in local :: uu____13963
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___101_13967 = env  in
       let uu____13968 = push1 s env.gamma  in
       {
         solver = (uu___101_13967.solver);
         range = (uu___101_13967.range);
         curmodule = (uu___101_13967.curmodule);
         gamma = uu____13968;
         gamma_cache = (uu___101_13967.gamma_cache);
         modules = (uu___101_13967.modules);
         expected_typ = (uu___101_13967.expected_typ);
         sigtab = (uu___101_13967.sigtab);
         is_pattern = (uu___101_13967.is_pattern);
         instantiate_imp = (uu___101_13967.instantiate_imp);
         effects = (uu___101_13967.effects);
         generalize = (uu___101_13967.generalize);
         letrecs = (uu___101_13967.letrecs);
         top_level = (uu___101_13967.top_level);
         check_uvars = (uu___101_13967.check_uvars);
         use_eq = (uu___101_13967.use_eq);
         is_iface = (uu___101_13967.is_iface);
         admit = (uu___101_13967.admit);
         lax = (uu___101_13967.lax);
         lax_universes = (uu___101_13967.lax_universes);
         failhard = (uu___101_13967.failhard);
         nosynth = (uu___101_13967.nosynth);
         tc_term = (uu___101_13967.tc_term);
         type_of = (uu___101_13967.type_of);
         universe_of = (uu___101_13967.universe_of);
         check_type_of = (uu___101_13967.check_type_of);
         use_bv_sorts = (uu___101_13967.use_bv_sorts);
         qtbl_name_and_index = (uu___101_13967.qtbl_name_and_index);
         proof_ns = (uu___101_13967.proof_ns);
         synth = (uu___101_13967.synth);
         splice = (uu___101_13967.splice);
         is_native_tactic = (uu___101_13967.is_native_tactic);
         identifier_info = (uu___101_13967.identifier_info);
         tc_hooks = (uu___101_13967.tc_hooks);
         dsenv = (uu___101_13967.dsenv);
         dep_graph = (uu___101_13967.dep_graph)
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
      let uu___102_13998 = env  in
      {
        solver = (uu___102_13998.solver);
        range = (uu___102_13998.range);
        curmodule = (uu___102_13998.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___102_13998.gamma_cache);
        modules = (uu___102_13998.modules);
        expected_typ = (uu___102_13998.expected_typ);
        sigtab = (uu___102_13998.sigtab);
        is_pattern = (uu___102_13998.is_pattern);
        instantiate_imp = (uu___102_13998.instantiate_imp);
        effects = (uu___102_13998.effects);
        generalize = (uu___102_13998.generalize);
        letrecs = (uu___102_13998.letrecs);
        top_level = (uu___102_13998.top_level);
        check_uvars = (uu___102_13998.check_uvars);
        use_eq = (uu___102_13998.use_eq);
        is_iface = (uu___102_13998.is_iface);
        admit = (uu___102_13998.admit);
        lax = (uu___102_13998.lax);
        lax_universes = (uu___102_13998.lax_universes);
        failhard = (uu___102_13998.failhard);
        nosynth = (uu___102_13998.nosynth);
        tc_term = (uu___102_13998.tc_term);
        type_of = (uu___102_13998.type_of);
        universe_of = (uu___102_13998.universe_of);
        check_type_of = (uu___102_13998.check_type_of);
        use_bv_sorts = (uu___102_13998.use_bv_sorts);
        qtbl_name_and_index = (uu___102_13998.qtbl_name_and_index);
        proof_ns = (uu___102_13998.proof_ns);
        synth = (uu___102_13998.synth);
        splice = (uu___102_13998.splice);
        is_native_tactic = (uu___102_13998.is_native_tactic);
        identifier_info = (uu___102_13998.identifier_info);
        tc_hooks = (uu___102_13998.tc_hooks);
        dsenv = (uu___102_13998.dsenv);
        dep_graph = (uu___102_13998.dep_graph)
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
            (let uu___103_14029 = env  in
             {
               solver = (uu___103_14029.solver);
               range = (uu___103_14029.range);
               curmodule = (uu___103_14029.curmodule);
               gamma = rest;
               gamma_cache = (uu___103_14029.gamma_cache);
               modules = (uu___103_14029.modules);
               expected_typ = (uu___103_14029.expected_typ);
               sigtab = (uu___103_14029.sigtab);
               is_pattern = (uu___103_14029.is_pattern);
               instantiate_imp = (uu___103_14029.instantiate_imp);
               effects = (uu___103_14029.effects);
               generalize = (uu___103_14029.generalize);
               letrecs = (uu___103_14029.letrecs);
               top_level = (uu___103_14029.top_level);
               check_uvars = (uu___103_14029.check_uvars);
               use_eq = (uu___103_14029.use_eq);
               is_iface = (uu___103_14029.is_iface);
               admit = (uu___103_14029.admit);
               lax = (uu___103_14029.lax);
               lax_universes = (uu___103_14029.lax_universes);
               failhard = (uu___103_14029.failhard);
               nosynth = (uu___103_14029.nosynth);
               tc_term = (uu___103_14029.tc_term);
               type_of = (uu___103_14029.type_of);
               universe_of = (uu___103_14029.universe_of);
               check_type_of = (uu___103_14029.check_type_of);
               use_bv_sorts = (uu___103_14029.use_bv_sorts);
               qtbl_name_and_index = (uu___103_14029.qtbl_name_and_index);
               proof_ns = (uu___103_14029.proof_ns);
               synth = (uu___103_14029.synth);
               splice = (uu___103_14029.splice);
               is_native_tactic = (uu___103_14029.is_native_tactic);
               identifier_info = (uu___103_14029.identifier_info);
               tc_hooks = (uu___103_14029.tc_hooks);
               dsenv = (uu___103_14029.dsenv);
               dep_graph = (uu___103_14029.dep_graph)
             }))
    | uu____14030 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____14052  ->
             match uu____14052 with | (x,uu____14058) -> push_bv env1 x) env
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
            let uu___104_14086 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___104_14086.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___104_14086.FStar_Syntax_Syntax.index);
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
      (let uu___105_14116 = env  in
       {
         solver = (uu___105_14116.solver);
         range = (uu___105_14116.range);
         curmodule = (uu___105_14116.curmodule);
         gamma = [];
         gamma_cache = (uu___105_14116.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___105_14116.sigtab);
         is_pattern = (uu___105_14116.is_pattern);
         instantiate_imp = (uu___105_14116.instantiate_imp);
         effects = (uu___105_14116.effects);
         generalize = (uu___105_14116.generalize);
         letrecs = (uu___105_14116.letrecs);
         top_level = (uu___105_14116.top_level);
         check_uvars = (uu___105_14116.check_uvars);
         use_eq = (uu___105_14116.use_eq);
         is_iface = (uu___105_14116.is_iface);
         admit = (uu___105_14116.admit);
         lax = (uu___105_14116.lax);
         lax_universes = (uu___105_14116.lax_universes);
         failhard = (uu___105_14116.failhard);
         nosynth = (uu___105_14116.nosynth);
         tc_term = (uu___105_14116.tc_term);
         type_of = (uu___105_14116.type_of);
         universe_of = (uu___105_14116.universe_of);
         check_type_of = (uu___105_14116.check_type_of);
         use_bv_sorts = (uu___105_14116.use_bv_sorts);
         qtbl_name_and_index = (uu___105_14116.qtbl_name_and_index);
         proof_ns = (uu___105_14116.proof_ns);
         synth = (uu___105_14116.synth);
         splice = (uu___105_14116.splice);
         is_native_tactic = (uu___105_14116.is_native_tactic);
         identifier_info = (uu___105_14116.identifier_info);
         tc_hooks = (uu___105_14116.tc_hooks);
         dsenv = (uu___105_14116.dsenv);
         dep_graph = (uu___105_14116.dep_graph)
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
        let uu____14148 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____14148 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____14176 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____14176)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___106_14189 = env  in
      {
        solver = (uu___106_14189.solver);
        range = (uu___106_14189.range);
        curmodule = (uu___106_14189.curmodule);
        gamma = (uu___106_14189.gamma);
        gamma_cache = (uu___106_14189.gamma_cache);
        modules = (uu___106_14189.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___106_14189.sigtab);
        is_pattern = (uu___106_14189.is_pattern);
        instantiate_imp = (uu___106_14189.instantiate_imp);
        effects = (uu___106_14189.effects);
        generalize = (uu___106_14189.generalize);
        letrecs = (uu___106_14189.letrecs);
        top_level = (uu___106_14189.top_level);
        check_uvars = (uu___106_14189.check_uvars);
        use_eq = false;
        is_iface = (uu___106_14189.is_iface);
        admit = (uu___106_14189.admit);
        lax = (uu___106_14189.lax);
        lax_universes = (uu___106_14189.lax_universes);
        failhard = (uu___106_14189.failhard);
        nosynth = (uu___106_14189.nosynth);
        tc_term = (uu___106_14189.tc_term);
        type_of = (uu___106_14189.type_of);
        universe_of = (uu___106_14189.universe_of);
        check_type_of = (uu___106_14189.check_type_of);
        use_bv_sorts = (uu___106_14189.use_bv_sorts);
        qtbl_name_and_index = (uu___106_14189.qtbl_name_and_index);
        proof_ns = (uu___106_14189.proof_ns);
        synth = (uu___106_14189.synth);
        splice = (uu___106_14189.splice);
        is_native_tactic = (uu___106_14189.is_native_tactic);
        identifier_info = (uu___106_14189.identifier_info);
        tc_hooks = (uu___106_14189.tc_hooks);
        dsenv = (uu___106_14189.dsenv);
        dep_graph = (uu___106_14189.dep_graph)
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
    let uu____14213 = expected_typ env_  in
    ((let uu___107_14219 = env_  in
      {
        solver = (uu___107_14219.solver);
        range = (uu___107_14219.range);
        curmodule = (uu___107_14219.curmodule);
        gamma = (uu___107_14219.gamma);
        gamma_cache = (uu___107_14219.gamma_cache);
        modules = (uu___107_14219.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___107_14219.sigtab);
        is_pattern = (uu___107_14219.is_pattern);
        instantiate_imp = (uu___107_14219.instantiate_imp);
        effects = (uu___107_14219.effects);
        generalize = (uu___107_14219.generalize);
        letrecs = (uu___107_14219.letrecs);
        top_level = (uu___107_14219.top_level);
        check_uvars = (uu___107_14219.check_uvars);
        use_eq = false;
        is_iface = (uu___107_14219.is_iface);
        admit = (uu___107_14219.admit);
        lax = (uu___107_14219.lax);
        lax_universes = (uu___107_14219.lax_universes);
        failhard = (uu___107_14219.failhard);
        nosynth = (uu___107_14219.nosynth);
        tc_term = (uu___107_14219.tc_term);
        type_of = (uu___107_14219.type_of);
        universe_of = (uu___107_14219.universe_of);
        check_type_of = (uu___107_14219.check_type_of);
        use_bv_sorts = (uu___107_14219.use_bv_sorts);
        qtbl_name_and_index = (uu___107_14219.qtbl_name_and_index);
        proof_ns = (uu___107_14219.proof_ns);
        synth = (uu___107_14219.synth);
        splice = (uu___107_14219.splice);
        is_native_tactic = (uu___107_14219.is_native_tactic);
        identifier_info = (uu___107_14219.identifier_info);
        tc_hooks = (uu___107_14219.tc_hooks);
        dsenv = (uu___107_14219.dsenv);
        dep_graph = (uu___107_14219.dep_graph)
      }), uu____14213)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____14232 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___81_14242  ->
                    match uu___81_14242 with
                    | Binding_sig (uu____14245,se) -> [se]
                    | uu____14251 -> []))
             in
          FStar_All.pipe_right uu____14232 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___108_14258 = env  in
       {
         solver = (uu___108_14258.solver);
         range = (uu___108_14258.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___108_14258.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___108_14258.expected_typ);
         sigtab = (uu___108_14258.sigtab);
         is_pattern = (uu___108_14258.is_pattern);
         instantiate_imp = (uu___108_14258.instantiate_imp);
         effects = (uu___108_14258.effects);
         generalize = (uu___108_14258.generalize);
         letrecs = (uu___108_14258.letrecs);
         top_level = (uu___108_14258.top_level);
         check_uvars = (uu___108_14258.check_uvars);
         use_eq = (uu___108_14258.use_eq);
         is_iface = (uu___108_14258.is_iface);
         admit = (uu___108_14258.admit);
         lax = (uu___108_14258.lax);
         lax_universes = (uu___108_14258.lax_universes);
         failhard = (uu___108_14258.failhard);
         nosynth = (uu___108_14258.nosynth);
         tc_term = (uu___108_14258.tc_term);
         type_of = (uu___108_14258.type_of);
         universe_of = (uu___108_14258.universe_of);
         check_type_of = (uu___108_14258.check_type_of);
         use_bv_sorts = (uu___108_14258.use_bv_sorts);
         qtbl_name_and_index = (uu___108_14258.qtbl_name_and_index);
         proof_ns = (uu___108_14258.proof_ns);
         synth = (uu___108_14258.synth);
         splice = (uu___108_14258.splice);
         is_native_tactic = (uu___108_14258.is_native_tactic);
         identifier_info = (uu___108_14258.identifier_info);
         tc_hooks = (uu___108_14258.tc_hooks);
         dsenv = (uu___108_14258.dsenv);
         dep_graph = (uu___108_14258.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14339)::tl1 -> aux out tl1
      | (Binding_lid (uu____14343,(uu____14344,t)))::tl1 ->
          let uu____14359 =
            let uu____14366 = FStar_Syntax_Free.uvars t  in
            ext out uu____14366  in
          aux uu____14359 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14373;
            FStar_Syntax_Syntax.index = uu____14374;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14381 =
            let uu____14388 = FStar_Syntax_Free.uvars t  in
            ext out uu____14388  in
          aux uu____14381 tl1
      | (Binding_sig uu____14395)::uu____14396 -> out
      | (Binding_sig_inst uu____14405)::uu____14406 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14461)::tl1 -> aux out tl1
      | (Binding_univ uu____14473)::tl1 -> aux out tl1
      | (Binding_lid (uu____14477,(uu____14478,t)))::tl1 ->
          let uu____14493 =
            let uu____14496 = FStar_Syntax_Free.univs t  in
            ext out uu____14496  in
          aux uu____14493 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14499;
            FStar_Syntax_Syntax.index = uu____14500;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14507 =
            let uu____14510 = FStar_Syntax_Free.univs t  in
            ext out uu____14510  in
          aux uu____14507 tl1
      | (Binding_sig uu____14513)::uu____14514 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14567)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14583 = FStar_Util.set_add uname out  in
          aux uu____14583 tl1
      | (Binding_lid (uu____14586,(uu____14587,t)))::tl1 ->
          let uu____14602 =
            let uu____14605 = FStar_Syntax_Free.univnames t  in
            ext out uu____14605  in
          aux uu____14602 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14608;
            FStar_Syntax_Syntax.index = uu____14609;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14616 =
            let uu____14619 = FStar_Syntax_Free.univnames t  in
            ext out uu____14619  in
          aux uu____14616 tl1
      | (Binding_sig uu____14622)::uu____14623 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___82_14647  ->
            match uu___82_14647 with
            | Binding_var x -> [x]
            | Binding_lid uu____14651 -> []
            | Binding_sig uu____14656 -> []
            | Binding_univ uu____14663 -> []
            | Binding_sig_inst uu____14664 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____14680 =
      let uu____14683 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14683
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14680 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____14705 =
      let uu____14706 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___83_14716  ->
                match uu___83_14716 with
                | Binding_var x ->
                    let uu____14718 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14718
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14721) ->
                    let uu____14722 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14722
                | Binding_sig (ls,uu____14724) ->
                    let uu____14729 =
                      let uu____14730 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14730
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14729
                | Binding_sig_inst (ls,uu____14740,uu____14741) ->
                    let uu____14746 =
                      let uu____14747 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14747
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14746))
         in
      FStar_All.pipe_right uu____14706 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14705 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____14764 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14764
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14792  ->
                 fun uu____14793  ->
                   match (uu____14792, uu____14793) with
                   | ((b1,uu____14811),(b2,uu____14813)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___84_14855  ->
    match uu___84_14855 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14856 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___85_14874  ->
             match uu___85_14874 with
             | Binding_sig (lids,uu____14880) -> FStar_List.append lids keys
             | uu____14885 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14891  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14925) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14944,uu____14945) -> false  in
      let uu____14954 =
        FStar_List.tryFind
          (fun uu____14972  ->
             match uu____14972 with | (p,uu____14980) -> list_prefix p path)
          env.proof_ns
         in
      match uu____14954 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14991,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15009 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____15009
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___109_15021 = e  in
        {
          solver = (uu___109_15021.solver);
          range = (uu___109_15021.range);
          curmodule = (uu___109_15021.curmodule);
          gamma = (uu___109_15021.gamma);
          gamma_cache = (uu___109_15021.gamma_cache);
          modules = (uu___109_15021.modules);
          expected_typ = (uu___109_15021.expected_typ);
          sigtab = (uu___109_15021.sigtab);
          is_pattern = (uu___109_15021.is_pattern);
          instantiate_imp = (uu___109_15021.instantiate_imp);
          effects = (uu___109_15021.effects);
          generalize = (uu___109_15021.generalize);
          letrecs = (uu___109_15021.letrecs);
          top_level = (uu___109_15021.top_level);
          check_uvars = (uu___109_15021.check_uvars);
          use_eq = (uu___109_15021.use_eq);
          is_iface = (uu___109_15021.is_iface);
          admit = (uu___109_15021.admit);
          lax = (uu___109_15021.lax);
          lax_universes = (uu___109_15021.lax_universes);
          failhard = (uu___109_15021.failhard);
          nosynth = (uu___109_15021.nosynth);
          tc_term = (uu___109_15021.tc_term);
          type_of = (uu___109_15021.type_of);
          universe_of = (uu___109_15021.universe_of);
          check_type_of = (uu___109_15021.check_type_of);
          use_bv_sorts = (uu___109_15021.use_bv_sorts);
          qtbl_name_and_index = (uu___109_15021.qtbl_name_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___109_15021.synth);
          splice = (uu___109_15021.splice);
          is_native_tactic = (uu___109_15021.is_native_tactic);
          identifier_info = (uu___109_15021.identifier_info);
          tc_hooks = (uu___109_15021.tc_hooks);
          dsenv = (uu___109_15021.dsenv);
          dep_graph = (uu___109_15021.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___110_15047 = e  in
      {
        solver = (uu___110_15047.solver);
        range = (uu___110_15047.range);
        curmodule = (uu___110_15047.curmodule);
        gamma = (uu___110_15047.gamma);
        gamma_cache = (uu___110_15047.gamma_cache);
        modules = (uu___110_15047.modules);
        expected_typ = (uu___110_15047.expected_typ);
        sigtab = (uu___110_15047.sigtab);
        is_pattern = (uu___110_15047.is_pattern);
        instantiate_imp = (uu___110_15047.instantiate_imp);
        effects = (uu___110_15047.effects);
        generalize = (uu___110_15047.generalize);
        letrecs = (uu___110_15047.letrecs);
        top_level = (uu___110_15047.top_level);
        check_uvars = (uu___110_15047.check_uvars);
        use_eq = (uu___110_15047.use_eq);
        is_iface = (uu___110_15047.is_iface);
        admit = (uu___110_15047.admit);
        lax = (uu___110_15047.lax);
        lax_universes = (uu___110_15047.lax_universes);
        failhard = (uu___110_15047.failhard);
        nosynth = (uu___110_15047.nosynth);
        tc_term = (uu___110_15047.tc_term);
        type_of = (uu___110_15047.type_of);
        universe_of = (uu___110_15047.universe_of);
        check_type_of = (uu___110_15047.check_type_of);
        use_bv_sorts = (uu___110_15047.use_bv_sorts);
        qtbl_name_and_index = (uu___110_15047.qtbl_name_and_index);
        proof_ns = ns;
        synth = (uu___110_15047.synth);
        splice = (uu___110_15047.splice);
        is_native_tactic = (uu___110_15047.is_native_tactic);
        identifier_info = (uu___110_15047.identifier_info);
        tc_hooks = (uu___110_15047.tc_hooks);
        dsenv = (uu___110_15047.dsenv);
        dep_graph = (uu___110_15047.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____15058 = FStar_Syntax_Free.names t  in
      let uu____15061 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____15058 uu____15061
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____15078 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____15078
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____15084 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____15084
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____15099 =
      match uu____15099 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____15115 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____15115)
       in
    let uu____15117 =
      let uu____15120 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____15120 FStar_List.rev  in
    FStar_All.pipe_right uu____15117 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____15137  -> ());
    push = (fun uu____15139  -> ());
    pop = (fun uu____15141  -> ());
    encode_modul = (fun uu____15144  -> fun uu____15145  -> ());
    encode_sig = (fun uu____15148  -> fun uu____15149  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____15155 =
             let uu____15162 = FStar_Options.peek ()  in (e, g, uu____15162)
              in
           [uu____15155]);
    solve = (fun uu____15178  -> fun uu____15179  -> fun uu____15180  -> ());
    finish = (fun uu____15186  -> ());
    refresh = (fun uu____15188  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___111_15192 = en  in
    let uu____15193 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____15196 = FStar_Util.smap_copy en.sigtab  in
    let uu____15199 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___111_15192.solver);
      range = (uu___111_15192.range);
      curmodule = (uu___111_15192.curmodule);
      gamma = (uu___111_15192.gamma);
      gamma_cache = uu____15193;
      modules = (uu___111_15192.modules);
      expected_typ = (uu___111_15192.expected_typ);
      sigtab = uu____15196;
      is_pattern = (uu___111_15192.is_pattern);
      instantiate_imp = (uu___111_15192.instantiate_imp);
      effects = (uu___111_15192.effects);
      generalize = (uu___111_15192.generalize);
      letrecs = (uu___111_15192.letrecs);
      top_level = (uu___111_15192.top_level);
      check_uvars = (uu___111_15192.check_uvars);
      use_eq = (uu___111_15192.use_eq);
      is_iface = (uu___111_15192.is_iface);
      admit = (uu___111_15192.admit);
      lax = (uu___111_15192.lax);
      lax_universes = (uu___111_15192.lax_universes);
      failhard = (uu___111_15192.failhard);
      nosynth = (uu___111_15192.nosynth);
      tc_term = (uu___111_15192.tc_term);
      type_of = (uu___111_15192.type_of);
      universe_of = (uu___111_15192.universe_of);
      check_type_of = (uu___111_15192.check_type_of);
      use_bv_sorts = (uu___111_15192.use_bv_sorts);
      qtbl_name_and_index = (uu___111_15192.qtbl_name_and_index);
      proof_ns = (uu___111_15192.proof_ns);
      synth = (uu___111_15192.synth);
      splice = (uu___111_15192.splice);
      is_native_tactic = (uu___111_15192.is_native_tactic);
      identifier_info = (uu___111_15192.identifier_info);
      tc_hooks = (uu___111_15192.tc_hooks);
      dsenv = uu____15199;
      dep_graph = (uu___111_15192.dep_graph)
    }
  