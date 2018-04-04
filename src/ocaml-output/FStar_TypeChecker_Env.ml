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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__universe_of
  
let __proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
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
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_type_of
  
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_bv_sorts
  
let __proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
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
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qtbl_name_and_index
  
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__proof_ns
  
let __proj__Mkenv__item__synth_hook :
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth_hook
  
let __proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list
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
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__splice
  
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
  
let __proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env =
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
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
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
           (fun uu___73_6141  ->
              match uu___73_6141 with
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
                         let uu___88_6151 = y1  in
                         let uu____6152 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___88_6151.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___88_6151.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____6152
                         }  in
                       Binding_var uu____6150
                   | uu____6155 -> failwith "Not a renaming")
              | b -> b))
  
let rename_env : FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___89_6163 = env  in
      let uu____6164 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___89_6163.solver);
        range = (uu___89_6163.range);
        curmodule = (uu___89_6163.curmodule);
        gamma = uu____6164;
        gamma_cache = (uu___89_6163.gamma_cache);
        modules = (uu___89_6163.modules);
        expected_typ = (uu___89_6163.expected_typ);
        sigtab = (uu___89_6163.sigtab);
        is_pattern = (uu___89_6163.is_pattern);
        instantiate_imp = (uu___89_6163.instantiate_imp);
        effects = (uu___89_6163.effects);
        generalize = (uu___89_6163.generalize);
        letrecs = (uu___89_6163.letrecs);
        top_level = (uu___89_6163.top_level);
        check_uvars = (uu___89_6163.check_uvars);
        use_eq = (uu___89_6163.use_eq);
        is_iface = (uu___89_6163.is_iface);
        admit = (uu___89_6163.admit);
        lax = (uu___89_6163.lax);
        lax_universes = (uu___89_6163.lax_universes);
        failhard = (uu___89_6163.failhard);
        nosynth = (uu___89_6163.nosynth);
        tc_term = (uu___89_6163.tc_term);
        type_of = (uu___89_6163.type_of);
        universe_of = (uu___89_6163.universe_of);
        check_type_of = (uu___89_6163.check_type_of);
        use_bv_sorts = (uu___89_6163.use_bv_sorts);
        qtbl_name_and_index = (uu___89_6163.qtbl_name_and_index);
        proof_ns = (uu___89_6163.proof_ns);
        synth_hook = (uu___89_6163.synth_hook);
        splice = (uu___89_6163.splice);
        is_native_tactic = (uu___89_6163.is_native_tactic);
        identifier_info = (uu___89_6163.identifier_info);
        tc_hooks = (uu___89_6163.tc_hooks);
        dsenv = (uu___89_6163.dsenv);
        dep_graph = (uu___89_6163.dep_graph)
      }
  
let default_tc_hooks : tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____6171  -> fun uu____6172  -> ()) } 
let tc_hooks : env -> tcenv_hooks = fun env  -> env.tc_hooks 
let set_tc_hooks : env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___90_6182 = env  in
      {
        solver = (uu___90_6182.solver);
        range = (uu___90_6182.range);
        curmodule = (uu___90_6182.curmodule);
        gamma = (uu___90_6182.gamma);
        gamma_cache = (uu___90_6182.gamma_cache);
        modules = (uu___90_6182.modules);
        expected_typ = (uu___90_6182.expected_typ);
        sigtab = (uu___90_6182.sigtab);
        is_pattern = (uu___90_6182.is_pattern);
        instantiate_imp = (uu___90_6182.instantiate_imp);
        effects = (uu___90_6182.effects);
        generalize = (uu___90_6182.generalize);
        letrecs = (uu___90_6182.letrecs);
        top_level = (uu___90_6182.top_level);
        check_uvars = (uu___90_6182.check_uvars);
        use_eq = (uu___90_6182.use_eq);
        is_iface = (uu___90_6182.is_iface);
        admit = (uu___90_6182.admit);
        lax = (uu___90_6182.lax);
        lax_universes = (uu___90_6182.lax_universes);
        failhard = (uu___90_6182.failhard);
        nosynth = (uu___90_6182.nosynth);
        tc_term = (uu___90_6182.tc_term);
        type_of = (uu___90_6182.type_of);
        universe_of = (uu___90_6182.universe_of);
        check_type_of = (uu___90_6182.check_type_of);
        use_bv_sorts = (uu___90_6182.use_bv_sorts);
        qtbl_name_and_index = (uu___90_6182.qtbl_name_and_index);
        proof_ns = (uu___90_6182.proof_ns);
        synth_hook = (uu___90_6182.synth_hook);
        splice = (uu___90_6182.splice);
        is_native_tactic = (uu___90_6182.is_native_tactic);
        identifier_info = (uu___90_6182.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___90_6182.dsenv);
        dep_graph = (uu___90_6182.dep_graph)
      }
  
let set_dep_graph : env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___91_6189 = e  in
      {
        solver = (uu___91_6189.solver);
        range = (uu___91_6189.range);
        curmodule = (uu___91_6189.curmodule);
        gamma = (uu___91_6189.gamma);
        gamma_cache = (uu___91_6189.gamma_cache);
        modules = (uu___91_6189.modules);
        expected_typ = (uu___91_6189.expected_typ);
        sigtab = (uu___91_6189.sigtab);
        is_pattern = (uu___91_6189.is_pattern);
        instantiate_imp = (uu___91_6189.instantiate_imp);
        effects = (uu___91_6189.effects);
        generalize = (uu___91_6189.generalize);
        letrecs = (uu___91_6189.letrecs);
        top_level = (uu___91_6189.top_level);
        check_uvars = (uu___91_6189.check_uvars);
        use_eq = (uu___91_6189.use_eq);
        is_iface = (uu___91_6189.is_iface);
        admit = (uu___91_6189.admit);
        lax = (uu___91_6189.lax);
        lax_universes = (uu___91_6189.lax_universes);
        failhard = (uu___91_6189.failhard);
        nosynth = (uu___91_6189.nosynth);
        tc_term = (uu___91_6189.tc_term);
        type_of = (uu___91_6189.type_of);
        universe_of = (uu___91_6189.universe_of);
        check_type_of = (uu___91_6189.check_type_of);
        use_bv_sorts = (uu___91_6189.use_bv_sorts);
        qtbl_name_and_index = (uu___91_6189.qtbl_name_and_index);
        proof_ns = (uu___91_6189.proof_ns);
        synth_hook = (uu___91_6189.synth_hook);
        splice = (uu___91_6189.splice);
        is_native_tactic = (uu___91_6189.is_native_tactic);
        identifier_info = (uu___91_6189.identifier_info);
        tc_hooks = (uu___91_6189.tc_hooks);
        dsenv = (uu___91_6189.dsenv);
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
      | (NoDelta ,uu____6204) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____6205,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____6206,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____6207 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab : 'Auu____6214 . Prims.unit -> 'Auu____6214 FStar_Util.smap =
  fun uu____6220  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache :
  'Auu____6223 . Prims.unit -> 'Auu____6223 FStar_Util.smap =
  fun uu____6229  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
            -> solver_t -> FStar_Ident.lident -> env
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
                  synth_hook =
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
  
let dsenv : env -> FStar_Syntax_DsEnv.env = fun env  -> env.dsenv 
let sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab 
let gamma_cache : env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache 
let query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]] 
let push_query_indices : Prims.unit -> Prims.unit =
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
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____6695  ->
    let uu____6696 = FStar_ST.op_Bang query_indices  in
    match uu____6696 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____6809  ->
    match uu____6809 with
    | (l,n1) ->
        let uu____6816 = FStar_ST.op_Bang query_indices  in
        (match uu____6816 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6927 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6944  ->
    let uu____6945 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6945
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____7016 =
       let uu____7019 = FStar_ST.op_Bang stack  in env :: uu____7019  in
     FStar_ST.op_Colon_Equals stack uu____7016);
    (let uu___92_7068 = env  in
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
       solver = (uu___92_7068.solver);
       range = (uu___92_7068.range);
       curmodule = (uu___92_7068.curmodule);
       gamma = (uu___92_7068.gamma);
       gamma_cache = uu____7069;
       modules = (uu___92_7068.modules);
       expected_typ = (uu___92_7068.expected_typ);
       sigtab = uu____7072;
       is_pattern = (uu___92_7068.is_pattern);
       instantiate_imp = (uu___92_7068.instantiate_imp);
       effects = (uu___92_7068.effects);
       generalize = (uu___92_7068.generalize);
       letrecs = (uu___92_7068.letrecs);
       top_level = (uu___92_7068.top_level);
       check_uvars = (uu___92_7068.check_uvars);
       use_eq = (uu___92_7068.use_eq);
       is_iface = (uu___92_7068.is_iface);
       admit = (uu___92_7068.admit);
       lax = (uu___92_7068.lax);
       lax_universes = (uu___92_7068.lax_universes);
       failhard = (uu___92_7068.failhard);
       nosynth = (uu___92_7068.nosynth);
       tc_term = (uu___92_7068.tc_term);
       type_of = (uu___92_7068.type_of);
       universe_of = (uu___92_7068.universe_of);
       check_type_of = (uu___92_7068.check_type_of);
       use_bv_sorts = (uu___92_7068.use_bv_sorts);
       qtbl_name_and_index = uu____7075;
       proof_ns = (uu___92_7068.proof_ns);
       synth_hook = (uu___92_7068.synth_hook);
       splice = (uu___92_7068.splice);
       is_native_tactic = (uu___92_7068.is_native_tactic);
       identifier_info = uu____7157;
       tc_hooks = (uu___92_7068.tc_hooks);
       dsenv = (uu___92_7068.dsenv);
       dep_graph = (uu___92_7068.dep_graph)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____7204  ->
    let uu____7205 = FStar_ST.op_Bang stack  in
    match uu____7205 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____7259 -> failwith "Impossible: Too many pops"
  
let push : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let pop : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let incr_query_index : env -> env =
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
              (let uu___93_7360 = env  in
               {
                 solver = (uu___93_7360.solver);
                 range = (uu___93_7360.range);
                 curmodule = (uu___93_7360.curmodule);
                 gamma = (uu___93_7360.gamma);
                 gamma_cache = (uu___93_7360.gamma_cache);
                 modules = (uu___93_7360.modules);
                 expected_typ = (uu___93_7360.expected_typ);
                 sigtab = (uu___93_7360.sigtab);
                 is_pattern = (uu___93_7360.is_pattern);
                 instantiate_imp = (uu___93_7360.instantiate_imp);
                 effects = (uu___93_7360.effects);
                 generalize = (uu___93_7360.generalize);
                 letrecs = (uu___93_7360.letrecs);
                 top_level = (uu___93_7360.top_level);
                 check_uvars = (uu___93_7360.check_uvars);
                 use_eq = (uu___93_7360.use_eq);
                 is_iface = (uu___93_7360.is_iface);
                 admit = (uu___93_7360.admit);
                 lax = (uu___93_7360.lax);
                 lax_universes = (uu___93_7360.lax_universes);
                 failhard = (uu___93_7360.failhard);
                 nosynth = (uu___93_7360.nosynth);
                 tc_term = (uu___93_7360.tc_term);
                 type_of = (uu___93_7360.type_of);
                 universe_of = (uu___93_7360.universe_of);
                 check_type_of = (uu___93_7360.check_type_of);
                 use_bv_sorts = (uu___93_7360.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___93_7360.proof_ns);
                 synth_hook = (uu___93_7360.synth_hook);
                 splice = (uu___93_7360.splice);
                 is_native_tactic = (uu___93_7360.is_native_tactic);
                 identifier_info = (uu___93_7360.identifier_info);
                 tc_hooks = (uu___93_7360.tc_hooks);
                 dsenv = (uu___93_7360.dsenv);
                 dep_graph = (uu___93_7360.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____7373,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___94_7382 = env  in
               {
                 solver = (uu___94_7382.solver);
                 range = (uu___94_7382.range);
                 curmodule = (uu___94_7382.curmodule);
                 gamma = (uu___94_7382.gamma);
                 gamma_cache = (uu___94_7382.gamma_cache);
                 modules = (uu___94_7382.modules);
                 expected_typ = (uu___94_7382.expected_typ);
                 sigtab = (uu___94_7382.sigtab);
                 is_pattern = (uu___94_7382.is_pattern);
                 instantiate_imp = (uu___94_7382.instantiate_imp);
                 effects = (uu___94_7382.effects);
                 generalize = (uu___94_7382.generalize);
                 letrecs = (uu___94_7382.letrecs);
                 top_level = (uu___94_7382.top_level);
                 check_uvars = (uu___94_7382.check_uvars);
                 use_eq = (uu___94_7382.use_eq);
                 is_iface = (uu___94_7382.is_iface);
                 admit = (uu___94_7382.admit);
                 lax = (uu___94_7382.lax);
                 lax_universes = (uu___94_7382.lax_universes);
                 failhard = (uu___94_7382.failhard);
                 nosynth = (uu___94_7382.nosynth);
                 tc_term = (uu___94_7382.tc_term);
                 type_of = (uu___94_7382.type_of);
                 universe_of = (uu___94_7382.universe_of);
                 check_type_of = (uu___94_7382.check_type_of);
                 use_bv_sorts = (uu___94_7382.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___94_7382.proof_ns);
                 synth_hook = (uu___94_7382.synth_hook);
                 splice = (uu___94_7382.splice);
                 is_native_tactic = (uu___94_7382.is_native_tactic);
                 identifier_info = (uu___94_7382.identifier_info);
                 tc_hooks = (uu___94_7382.tc_hooks);
                 dsenv = (uu___94_7382.dsenv);
                 dep_graph = (uu___94_7382.dep_graph)
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
        (let uu___95_7408 = e  in
         {
           solver = (uu___95_7408.solver);
           range = r;
           curmodule = (uu___95_7408.curmodule);
           gamma = (uu___95_7408.gamma);
           gamma_cache = (uu___95_7408.gamma_cache);
           modules = (uu___95_7408.modules);
           expected_typ = (uu___95_7408.expected_typ);
           sigtab = (uu___95_7408.sigtab);
           is_pattern = (uu___95_7408.is_pattern);
           instantiate_imp = (uu___95_7408.instantiate_imp);
           effects = (uu___95_7408.effects);
           generalize = (uu___95_7408.generalize);
           letrecs = (uu___95_7408.letrecs);
           top_level = (uu___95_7408.top_level);
           check_uvars = (uu___95_7408.check_uvars);
           use_eq = (uu___95_7408.use_eq);
           is_iface = (uu___95_7408.is_iface);
           admit = (uu___95_7408.admit);
           lax = (uu___95_7408.lax);
           lax_universes = (uu___95_7408.lax_universes);
           failhard = (uu___95_7408.failhard);
           nosynth = (uu___95_7408.nosynth);
           tc_term = (uu___95_7408.tc_term);
           type_of = (uu___95_7408.type_of);
           universe_of = (uu___95_7408.universe_of);
           check_type_of = (uu___95_7408.check_type_of);
           use_bv_sorts = (uu___95_7408.use_bv_sorts);
           qtbl_name_and_index = (uu___95_7408.qtbl_name_and_index);
           proof_ns = (uu___95_7408.proof_ns);
           synth_hook = (uu___95_7408.synth_hook);
           splice = (uu___95_7408.splice);
           is_native_tactic = (uu___95_7408.is_native_tactic);
           identifier_info = (uu___95_7408.identifier_info);
           tc_hooks = (uu___95_7408.tc_hooks);
           dsenv = (uu___95_7408.dsenv);
           dep_graph = (uu___95_7408.dep_graph)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let toggle_id_info : env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____7418 =
        let uu____7419 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____7419 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7418
  
let insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____7467 =
          let uu____7468 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____7468 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7467
  
let insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____7516 =
          let uu____7517 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____7517 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7516
  
let promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____7567 =
        let uu____7568 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____7568 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7567
  
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___96_7621 = env  in
      {
        solver = (uu___96_7621.solver);
        range = (uu___96_7621.range);
        curmodule = lid;
        gamma = (uu___96_7621.gamma);
        gamma_cache = (uu___96_7621.gamma_cache);
        modules = (uu___96_7621.modules);
        expected_typ = (uu___96_7621.expected_typ);
        sigtab = (uu___96_7621.sigtab);
        is_pattern = (uu___96_7621.is_pattern);
        instantiate_imp = (uu___96_7621.instantiate_imp);
        effects = (uu___96_7621.effects);
        generalize = (uu___96_7621.generalize);
        letrecs = (uu___96_7621.letrecs);
        top_level = (uu___96_7621.top_level);
        check_uvars = (uu___96_7621.check_uvars);
        use_eq = (uu___96_7621.use_eq);
        is_iface = (uu___96_7621.is_iface);
        admit = (uu___96_7621.admit);
        lax = (uu___96_7621.lax);
        lax_universes = (uu___96_7621.lax_universes);
        failhard = (uu___96_7621.failhard);
        nosynth = (uu___96_7621.nosynth);
        tc_term = (uu___96_7621.tc_term);
        type_of = (uu___96_7621.type_of);
        universe_of = (uu___96_7621.universe_of);
        check_type_of = (uu___96_7621.check_type_of);
        use_bv_sorts = (uu___96_7621.use_bv_sorts);
        qtbl_name_and_index = (uu___96_7621.qtbl_name_and_index);
        proof_ns = (uu___96_7621.proof_ns);
        synth_hook = (uu___96_7621.synth_hook);
        splice = (uu___96_7621.splice);
        is_native_tactic = (uu___96_7621.is_native_tactic);
        identifier_info = (uu___96_7621.identifier_info);
        tc_hooks = (uu___96_7621.tc_hooks);
        dsenv = (uu___96_7621.dsenv);
        dep_graph = (uu___96_7621.dep_graph)
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
      let uu____7640 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____7640
  
let name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____7648 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7648)
  
let variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____7656 =
      let uu____7657 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7657  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7656)
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7660  ->
    let uu____7661 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7661
  
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
      | ((formals,t),uu____7699) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7723 = FStar_Syntax_Subst.subst vs t  in (us, uu____7723)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___74_7736  ->
    match uu___74_7736 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7760  -> new_u_univ ()))
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
      let uu____7773 = inst_tscheme t  in
      match uu____7773 with
      | (us,t1) ->
          let uu____7784 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7784)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7796  ->
          match uu____7796 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7811 =
                         let uu____7812 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7813 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7814 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7815 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7812 uu____7813 uu____7814 uu____7815
                          in
                       failwith uu____7811)
                    else ();
                    (let uu____7817 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7817))
               | uu____7824 ->
                   let uu____7825 =
                     let uu____7826 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7826
                      in
                   failwith uu____7825)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7830 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7834 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7838 -> false
  
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
             | ([],uu____7872) -> Maybe
             | (uu____7879,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7898 -> No  in
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
let lookup_qname : env -> FStar_Ident.lident -> qninfo =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____7983 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7983 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___75_8029  ->
                   match uu___75_8029 with
                   | Binding_lid (l,t) ->
                       let uu____8052 = FStar_Ident.lid_equals lid l  in
                       if uu____8052
                       then
                         let uu____8073 =
                           let uu____8092 =
                             let uu____8107 = inst_tscheme t  in
                             FStar_Util.Inl uu____8107  in
                           let uu____8122 = FStar_Ident.range_of_lid l  in
                           (uu____8092, uu____8122)  in
                         FStar_Pervasives_Native.Some uu____8073
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____8174,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____8176);
                                     FStar_Syntax_Syntax.sigrng = uu____8177;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____8178;
                                     FStar_Syntax_Syntax.sigmeta = uu____8179;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____8180;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____8200 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____8200
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____8246 ->
                             FStar_Pervasives_Native.Some t
                         | uu____8253 -> cache t  in
                       let uu____8254 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____8254 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____8296 =
                              let uu____8297 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                uu____8297)
                               in
                            maybe_cache uu____8296)
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____8331 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____8331 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____8373 =
                              let uu____8392 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                uu____8392)
                               in
                            FStar_Pervasives_Native.Some uu____8373)
                   | uu____8437 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____8497 = find_in_sigtab env lid  in
         match uu____8497 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8576) ->
          add_sigelts env ses
      | uu____8585 ->
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
            | uu____8599 -> ()))

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
        (fun uu___76_8626  ->
           match uu___76_8626 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8644 -> FStar_Pervasives_Native.None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____8697,lb::[]),uu____8699) ->
            let uu____8712 =
              let uu____8721 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____8730 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____8721, uu____8730)  in
            FStar_Pervasives_Native.Some uu____8712
        | FStar_Syntax_Syntax.Sig_let ((uu____8743,lbs),uu____8745) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____8781 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____8793 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____8793
                     then
                       let uu____8804 =
                         let uu____8813 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____8822 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____8813, uu____8822)  in
                       FStar_Pervasives_Native.Some uu____8804
                     else FStar_Pervasives_Native.None)
        | uu____8844 -> FStar_Pervasives_Native.None
  
let effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____8897 =
            let uu____8906 =
              let uu____8911 =
                let uu____8912 =
                  let uu____8915 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____8915
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____8912)  in
              inst_tscheme1 uu____8911  in
            (uu____8906, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8897
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____8935,uu____8936) ->
          let uu____8941 =
            let uu____8950 =
              let uu____8955 =
                let uu____8956 =
                  let uu____8959 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____8959  in
                (us, uu____8956)  in
              inst_tscheme1 uu____8955  in
            (uu____8950, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8941
      | uu____8976 -> FStar_Pervasives_Native.None
  
let try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                          FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____9054 =
          match uu____9054 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____9150,uvs,t,uu____9153,uu____9154,uu____9155);
                      FStar_Syntax_Syntax.sigrng = uu____9156;
                      FStar_Syntax_Syntax.sigquals = uu____9157;
                      FStar_Syntax_Syntax.sigmeta = uu____9158;
                      FStar_Syntax_Syntax.sigattrs = uu____9159;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____9180 =
                     let uu____9189 = inst_tscheme1 (uvs, t)  in
                     (uu____9189, rng)  in
                   FStar_Pervasives_Native.Some uu____9180
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____9209;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____9211;
                      FStar_Syntax_Syntax.sigattrs = uu____9212;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____9229 =
                     let uu____9230 = in_cur_mod env l  in uu____9230 = Yes
                      in
                   if uu____9229
                   then
                     let uu____9241 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____9241
                      then
                        let uu____9254 =
                          let uu____9263 = inst_tscheme1 (uvs, t)  in
                          (uu____9263, rng)  in
                        FStar_Pervasives_Native.Some uu____9254
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9290 =
                        let uu____9299 = inst_tscheme1 (uvs, t)  in
                        (uu____9299, rng)  in
                      FStar_Pervasives_Native.Some uu____9290)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9320,uu____9321);
                      FStar_Syntax_Syntax.sigrng = uu____9322;
                      FStar_Syntax_Syntax.sigquals = uu____9323;
                      FStar_Syntax_Syntax.sigmeta = uu____9324;
                      FStar_Syntax_Syntax.sigattrs = uu____9325;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____9364 =
                          let uu____9373 = inst_tscheme1 (uvs, k)  in
                          (uu____9373, rng)  in
                        FStar_Pervasives_Native.Some uu____9364
                    | uu____9390 ->
                        let uu____9391 =
                          let uu____9400 =
                            let uu____9405 =
                              let uu____9406 =
                                let uu____9409 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9409
                                 in
                              (uvs, uu____9406)  in
                            inst_tscheme1 uu____9405  in
                          (uu____9400, rng)  in
                        FStar_Pervasives_Native.Some uu____9391)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9430,uu____9431);
                      FStar_Syntax_Syntax.sigrng = uu____9432;
                      FStar_Syntax_Syntax.sigquals = uu____9433;
                      FStar_Syntax_Syntax.sigmeta = uu____9434;
                      FStar_Syntax_Syntax.sigattrs = uu____9435;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____9475 =
                          let uu____9484 = inst_tscheme_with (uvs, k) us  in
                          (uu____9484, rng)  in
                        FStar_Pervasives_Native.Some uu____9475
                    | uu____9501 ->
                        let uu____9502 =
                          let uu____9511 =
                            let uu____9516 =
                              let uu____9517 =
                                let uu____9520 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9520
                                 in
                              (uvs, uu____9517)  in
                            inst_tscheme_with uu____9516 us  in
                          (uu____9511, rng)  in
                        FStar_Pervasives_Native.Some uu____9502)
               | FStar_Util.Inr se ->
                   let uu____9554 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____9575;
                          FStar_Syntax_Syntax.sigrng = uu____9576;
                          FStar_Syntax_Syntax.sigquals = uu____9577;
                          FStar_Syntax_Syntax.sigmeta = uu____9578;
                          FStar_Syntax_Syntax.sigattrs = uu____9579;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____9594 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____9554
                     (FStar_Util.map_option
                        (fun uu____9642  ->
                           match uu____9642 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____9673 =
          let uu____9684 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____9684 mapper  in
        match uu____9673 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____9758 =
              let uu____9769 =
                let uu____9776 =
                  let uu___97_9779 = t  in
                  let uu____9780 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___97_9779.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____9780;
                    FStar_Syntax_Syntax.vars =
                      (uu___97_9779.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____9776)  in
              (uu____9769, r)  in
            FStar_Pervasives_Native.Some uu____9758
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9823 = lookup_qname env l  in
      match uu____9823 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9842 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9890 = try_lookup_bv env bv  in
      match uu____9890 with
      | FStar_Pervasives_Native.None  ->
          let uu____9905 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9905 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9920 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9921 =
            let uu____9922 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9922  in
          (uu____9920, uu____9921)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9939 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____9939 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____10005 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____10005  in
          let uu____10006 =
            let uu____10015 =
              let uu____10020 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____10020)  in
            (uu____10015, r1)  in
          FStar_Pervasives_Native.Some uu____10006
  
let try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____10048 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____10048 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____10081,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____10106 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____10106  in
            let uu____10107 =
              let uu____10112 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____10112, r1)  in
            FStar_Pervasives_Native.Some uu____10107
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____10131 = try_lookup_lid env l  in
      match uu____10131 with
      | FStar_Pervasives_Native.None  ->
          let uu____10158 = name_not_found l  in
          let uu____10163 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____10158 uu____10163
      | FStar_Pervasives_Native.Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___77_10199  ->
              match uu___77_10199 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____10201 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____10216 = lookup_qname env lid  in
      match uu____10216 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10225,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____10228;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10230;
              FStar_Syntax_Syntax.sigattrs = uu____10231;_},FStar_Pervasives_Native.None
            ),uu____10232)
          ->
          let uu____10281 =
            let uu____10292 =
              let uu____10297 =
                let uu____10298 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____10298 t  in
              (uvs, uu____10297)  in
            (uu____10292, q)  in
          FStar_Pervasives_Native.Some uu____10281
      | uu____10315 -> FStar_Pervasives_Native.None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____10332 = lookup_qname env lid  in
      match uu____10332 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10337,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____10340;
              FStar_Syntax_Syntax.sigquals = uu____10341;
              FStar_Syntax_Syntax.sigmeta = uu____10342;
              FStar_Syntax_Syntax.sigattrs = uu____10343;_},FStar_Pervasives_Native.None
            ),uu____10344)
          ->
          let uu____10393 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____10393 (uvs, t)
      | uu____10394 ->
          let uu____10395 = name_not_found lid  in
          let uu____10400 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____10395 uu____10400
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____10415 = lookup_qname env lid  in
      match uu____10415 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10420,uvs,t,uu____10423,uu____10424,uu____10425);
              FStar_Syntax_Syntax.sigrng = uu____10426;
              FStar_Syntax_Syntax.sigquals = uu____10427;
              FStar_Syntax_Syntax.sigmeta = uu____10428;
              FStar_Syntax_Syntax.sigattrs = uu____10429;_},FStar_Pervasives_Native.None
            ),uu____10430)
          ->
          let uu____10483 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____10483 (uvs, t)
      | uu____10484 ->
          let uu____10485 = name_not_found lid  in
          let uu____10490 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____10485 uu____10490
  
let datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____10507 = lookup_qname env lid  in
      match uu____10507 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10514,uu____10515,uu____10516,uu____10517,uu____10518,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10520;
              FStar_Syntax_Syntax.sigquals = uu____10521;
              FStar_Syntax_Syntax.sigmeta = uu____10522;
              FStar_Syntax_Syntax.sigattrs = uu____10523;_},uu____10524),uu____10525)
          -> (true, dcs)
      | uu____10586 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____10595 = lookup_qname env lid  in
      match uu____10595 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10596,uu____10597,uu____10598,l,uu____10600,uu____10601);
              FStar_Syntax_Syntax.sigrng = uu____10602;
              FStar_Syntax_Syntax.sigquals = uu____10603;
              FStar_Syntax_Syntax.sigmeta = uu____10604;
              FStar_Syntax_Syntax.sigattrs = uu____10605;_},uu____10606),uu____10607)
          -> l
      | uu____10662 ->
          let uu____10663 =
            let uu____10664 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10664  in
          failwith uu____10663
  
let lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10705)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10756,lbs),uu____10758)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10786 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10786
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10818 -> FStar_Pervasives_Native.None)
        | uu____10823 -> FStar_Pervasives_Native.None
  
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
        let uu____10847 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____10847
  
let attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____10870),uu____10871) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____10920 -> FStar_Pervasives_Native.None
  
let lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____10937 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____10937
  
let try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10952 = lookup_qname env ftv  in
      match uu____10952 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10956) ->
          let uu____11001 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____11001 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____11022,t),r) ->
               let uu____11037 =
                 let uu____11038 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____11038 t  in
               FStar_Pervasives_Native.Some uu____11037)
      | uu____11039 -> FStar_Pervasives_Native.None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____11046 = try_lookup_effect_lid env ftv  in
      match uu____11046 with
      | FStar_Pervasives_Native.None  ->
          let uu____11049 = name_not_found ftv  in
          let uu____11054 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____11049 uu____11054
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
        let uu____11071 = lookup_qname env lid0  in
        match uu____11071 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____11082);
                FStar_Syntax_Syntax.sigrng = uu____11083;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____11085;
                FStar_Syntax_Syntax.sigattrs = uu____11086;_},FStar_Pervasives_Native.None
              ),uu____11087)
            ->
            let lid1 =
              let uu____11141 =
                let uu____11142 = FStar_Ident.range_of_lid lid  in
                let uu____11143 =
                  let uu____11144 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____11144  in
                FStar_Range.set_use_range uu____11142 uu____11143  in
              FStar_Ident.set_lid_range lid uu____11141  in
            let uu____11145 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___78_11149  ->
                      match uu___78_11149 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11150 -> false))
               in
            if uu____11145
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____11164 =
                      let uu____11165 =
                        let uu____11166 = get_range env  in
                        FStar_Range.string_of_range uu____11166  in
                      let uu____11167 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____11168 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____11165 uu____11167 uu____11168
                       in
                    failwith uu____11164)
                  in
               match (binders, univs1) with
               | ([],uu____11175) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____11192,uu____11193::uu____11194::uu____11195) ->
                   let uu____11200 =
                     let uu____11201 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____11202 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____11201 uu____11202
                      in
                   failwith uu____11200
               | uu____11209 ->
                   let uu____11214 =
                     let uu____11219 =
                       let uu____11220 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____11220)  in
                     inst_tscheme_with uu____11219 insts  in
                   (match uu____11214 with
                    | (uu____11231,t) ->
                        let t1 =
                          let uu____11234 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____11234 t  in
                        let uu____11235 =
                          let uu____11236 = FStar_Syntax_Subst.compress t1
                             in
                          uu____11236.FStar_Syntax_Syntax.n  in
                        (match uu____11235 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____11283 -> failwith "Impossible")))
        | uu____11290 -> FStar_Pervasives_Native.None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____11310 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____11310 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____11323,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____11330 = find1 l2  in
            (match uu____11330 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____11337 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____11337 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____11341 = find1 l  in
            (match uu____11341 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      let uu____11346 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____11346
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____11356 = lookup_qname env l1  in
      match uu____11356 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____11359;
              FStar_Syntax_Syntax.sigrng = uu____11360;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11362;
              FStar_Syntax_Syntax.sigattrs = uu____11363;_},uu____11364),uu____11365)
          -> q
      | uu____11416 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____11429 =
          let uu____11430 =
            let uu____11431 = FStar_Util.string_of_int i  in
            let uu____11432 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____11431 uu____11432
             in
          failwith uu____11430  in
        let uu____11433 = lookup_datacon env lid  in
        match uu____11433 with
        | (uu____11438,t) ->
            let uu____11440 =
              let uu____11441 = FStar_Syntax_Subst.compress t  in
              uu____11441.FStar_Syntax_Syntax.n  in
            (match uu____11440 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11445) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____11476 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____11476
                      FStar_Pervasives_Native.fst)
             | uu____11485 -> fail1 ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11492 = lookup_qname env l  in
      match uu____11492 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11493,uu____11494,uu____11495);
              FStar_Syntax_Syntax.sigrng = uu____11496;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11498;
              FStar_Syntax_Syntax.sigattrs = uu____11499;_},uu____11500),uu____11501)
          ->
          FStar_Util.for_some
            (fun uu___79_11554  ->
               match uu___79_11554 with
               | FStar_Syntax_Syntax.Projector uu____11555 -> true
               | uu____11560 -> false) quals
      | uu____11561 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11568 = lookup_qname env lid  in
      match uu____11568 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11569,uu____11570,uu____11571,uu____11572,uu____11573,uu____11574);
              FStar_Syntax_Syntax.sigrng = uu____11575;
              FStar_Syntax_Syntax.sigquals = uu____11576;
              FStar_Syntax_Syntax.sigmeta = uu____11577;
              FStar_Syntax_Syntax.sigattrs = uu____11578;_},uu____11579),uu____11580)
          -> true
      | uu____11635 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11642 = lookup_qname env lid  in
      match uu____11642 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11643,uu____11644,uu____11645,uu____11646,uu____11647,uu____11648);
              FStar_Syntax_Syntax.sigrng = uu____11649;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11651;
              FStar_Syntax_Syntax.sigattrs = uu____11652;_},uu____11653),uu____11654)
          ->
          FStar_Util.for_some
            (fun uu___80_11715  ->
               match uu___80_11715 with
               | FStar_Syntax_Syntax.RecordType uu____11716 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11725 -> true
               | uu____11734 -> false) quals
      | uu____11735 -> false
  
let qninfo_is_action : qninfo -> Prims.bool =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____11739,uu____11740);
            FStar_Syntax_Syntax.sigrng = uu____11741;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____11743;
            FStar_Syntax_Syntax.sigattrs = uu____11744;_},uu____11745),uu____11746)
        ->
        FStar_Util.for_some
          (fun uu___81_11803  ->
             match uu___81_11803 with
             | FStar_Syntax_Syntax.Action uu____11804 -> true
             | uu____11805 -> false) quals
    | uu____11806 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11813 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____11813
  
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
      let uu____11823 =
        let uu____11824 = FStar_Syntax_Util.un_uinst head1  in
        uu____11824.FStar_Syntax_Syntax.n  in
      match uu____11823 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11828 -> false
  
let is_irreducible : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11835 = lookup_qname env l  in
      match uu____11835 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11837),uu____11838) ->
          FStar_Util.for_some
            (fun uu___82_11886  ->
               match uu___82_11886 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11887 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11888 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11953 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11969) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11986 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11993 ->
                 FStar_Pervasives_Native.Some true
             | uu____12010 -> FStar_Pervasives_Native.Some false)
         in
      let uu____12011 =
        let uu____12014 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____12014 mapper  in
      match uu____12011 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____12060 = lookup_qname env lid  in
      match uu____12060 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12061,uu____12062,tps,uu____12064,uu____12065,uu____12066);
              FStar_Syntax_Syntax.sigrng = uu____12067;
              FStar_Syntax_Syntax.sigquals = uu____12068;
              FStar_Syntax_Syntax.sigmeta = uu____12069;
              FStar_Syntax_Syntax.sigattrs = uu____12070;_},uu____12071),uu____12072)
          -> FStar_List.length tps
      | uu____12135 ->
          let uu____12136 = name_not_found lid  in
          let uu____12141 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12136 uu____12141
  
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
           (fun uu____12181  ->
              match uu____12181 with
              | (d,uu____12189) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____12200 = effect_decl_opt env l  in
      match uu____12200 with
      | FStar_Pervasives_Native.None  ->
          let uu____12215 = name_not_found l  in
          let uu____12220 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12215 uu____12220
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let identity_mlift : mlift =
  {
    mlift_wp = (fun uu____12242  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____12257  ->
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
        let uu____12282 = FStar_Ident.lid_equals l1 l2  in
        if uu____12282
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____12290 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____12290
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____12298 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____12351  ->
                        match uu____12351 with
                        | (m1,m2,uu____12364,uu____12365,uu____12366) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____12298 with
              | FStar_Pervasives_Native.None  ->
                  let uu____12383 =
                    let uu____12388 =
                      let uu____12389 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____12390 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____12389
                        uu____12390
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____12388)
                     in
                  FStar_Errors.raise_error uu____12383 env.range
              | FStar_Pervasives_Native.Some
                  (uu____12397,uu____12398,m3,j1,j2) -> (m3, j1, j2)))
  
let monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____12425 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____12425
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
  'Auu____12438 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12438)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12465 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12491  ->
                match uu____12491 with
                | (d,uu____12497) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____12465 with
      | FStar_Pervasives_Native.None  ->
          let uu____12508 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12508
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12521 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12521 with
           | (uu____12532,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12542)::(wp,uu____12544)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12580 -> failwith "Impossible"))
  
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
          let uu____12615 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____12615
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____12617 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____12617
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
                  let uu____12625 = get_range env  in
                  let uu____12626 =
                    let uu____12629 =
                      let uu____12630 =
                        let uu____12645 =
                          let uu____12648 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____12648]  in
                        (null_wp, uu____12645)  in
                      FStar_Syntax_Syntax.Tm_app uu____12630  in
                    FStar_Syntax_Syntax.mk uu____12629  in
                  uu____12626 FStar_Pervasives_Native.None uu____12625  in
                let uu____12654 =
                  let uu____12655 =
                    let uu____12664 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____12664]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____12655;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____12654))
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___98_12673 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___98_12673.order);
              joins = (uu___98_12673.joins)
            }  in
          let uu___99_12682 = env  in
          {
            solver = (uu___99_12682.solver);
            range = (uu___99_12682.range);
            curmodule = (uu___99_12682.curmodule);
            gamma = (uu___99_12682.gamma);
            gamma_cache = (uu___99_12682.gamma_cache);
            modules = (uu___99_12682.modules);
            expected_typ = (uu___99_12682.expected_typ);
            sigtab = (uu___99_12682.sigtab);
            is_pattern = (uu___99_12682.is_pattern);
            instantiate_imp = (uu___99_12682.instantiate_imp);
            effects;
            generalize = (uu___99_12682.generalize);
            letrecs = (uu___99_12682.letrecs);
            top_level = (uu___99_12682.top_level);
            check_uvars = (uu___99_12682.check_uvars);
            use_eq = (uu___99_12682.use_eq);
            is_iface = (uu___99_12682.is_iface);
            admit = (uu___99_12682.admit);
            lax = (uu___99_12682.lax);
            lax_universes = (uu___99_12682.lax_universes);
            failhard = (uu___99_12682.failhard);
            nosynth = (uu___99_12682.nosynth);
            tc_term = (uu___99_12682.tc_term);
            type_of = (uu___99_12682.type_of);
            universe_of = (uu___99_12682.universe_of);
            check_type_of = (uu___99_12682.check_type_of);
            use_bv_sorts = (uu___99_12682.use_bv_sorts);
            qtbl_name_and_index = (uu___99_12682.qtbl_name_and_index);
            proof_ns = (uu___99_12682.proof_ns);
            synth_hook = (uu___99_12682.synth_hook);
            splice = (uu___99_12682.splice);
            is_native_tactic = (uu___99_12682.is_native_tactic);
            identifier_info = (uu___99_12682.identifier_info);
            tc_hooks = (uu___99_12682.tc_hooks);
            dsenv = (uu___99_12682.dsenv);
            dep_graph = (uu___99_12682.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12702 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12702  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12816 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12817 = l1 u t wp e  in
                                l2 u t uu____12816 uu____12817))
                | uu____12818 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12866 = inst_tscheme_with lift_t [u]  in
            match uu____12866 with
            | (uu____12873,lift_t1) ->
                let uu____12875 =
                  let uu____12878 =
                    let uu____12879 =
                      let uu____12894 =
                        let uu____12897 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12898 =
                          let uu____12901 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12901]  in
                        uu____12897 :: uu____12898  in
                      (lift_t1, uu____12894)  in
                    FStar_Syntax_Syntax.Tm_app uu____12879  in
                  FStar_Syntax_Syntax.mk uu____12878  in
                uu____12875 FStar_Pervasives_Native.None
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
            let uu____12951 = inst_tscheme_with lift_t [u]  in
            match uu____12951 with
            | (uu____12958,lift_t1) ->
                let uu____12960 =
                  let uu____12963 =
                    let uu____12964 =
                      let uu____12979 =
                        let uu____12982 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12983 =
                          let uu____12986 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12987 =
                            let uu____12990 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12990]  in
                          uu____12986 :: uu____12987  in
                        uu____12982 :: uu____12983  in
                      (lift_t1, uu____12979)  in
                    FStar_Syntax_Syntax.Tm_app uu____12964  in
                  FStar_Syntax_Syntax.mk uu____12963  in
                uu____12960 FStar_Pervasives_Native.None
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
              let uu____13032 =
                let uu____13033 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____13033
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____13032  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____13037 =
              let uu____13038 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____13038  in
            let uu____13039 =
              let uu____13040 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____13062 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____13062)
                 in
              FStar_Util.dflt "none" uu____13040  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____13037
              uu____13039
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____13088  ->
                    match uu____13088 with
                    | (e,uu____13096) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____13115 =
            match uu____13115 with
            | (i,j) ->
                let uu____13126 = FStar_Ident.lid_equals i j  in
                if uu____13126
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
              let uu____13154 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____13164 = FStar_Ident.lid_equals i k  in
                        if uu____13164
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____13175 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____13175
                                  then []
                                  else
                                    (let uu____13179 =
                                       let uu____13188 =
                                         find_edge order1 (i, k)  in
                                       let uu____13191 =
                                         find_edge order1 (k, j)  in
                                       (uu____13188, uu____13191)  in
                                     match uu____13179 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____13206 =
                                           compose_edges e1 e2  in
                                         [uu____13206]
                                     | uu____13207 -> [])))))
                 in
              FStar_List.append order1 uu____13154  in
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
                   let uu____13237 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____13239 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____13239
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____13237
                   then
                     let uu____13244 =
                       let uu____13249 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____13249)
                        in
                     let uu____13250 = get_range env  in
                     FStar_Errors.raise_error uu____13244 uu____13250
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____13327 = FStar_Ident.lid_equals i j
                                   in
                                if uu____13327
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____13376 =
                                              let uu____13385 =
                                                find_edge order2 (i, k)  in
                                              let uu____13388 =
                                                find_edge order2 (j, k)  in
                                              (uu____13385, uu____13388)  in
                                            match uu____13376 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13430,uu____13431)
                                                     ->
                                                     let uu____13438 =
                                                       let uu____13443 =
                                                         let uu____13444 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13444
                                                          in
                                                       let uu____13447 =
                                                         let uu____13448 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____13448
                                                          in
                                                       (uu____13443,
                                                         uu____13447)
                                                        in
                                                     (match uu____13438 with
                                                      | (true ,true ) ->
                                                          let uu____13459 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____13459
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
                                            | uu____13484 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___100_13557 = env.effects  in
              { decls = (uu___100_13557.decls); order = order2; joins }  in
            let uu___101_13558 = env  in
            {
              solver = (uu___101_13558.solver);
              range = (uu___101_13558.range);
              curmodule = (uu___101_13558.curmodule);
              gamma = (uu___101_13558.gamma);
              gamma_cache = (uu___101_13558.gamma_cache);
              modules = (uu___101_13558.modules);
              expected_typ = (uu___101_13558.expected_typ);
              sigtab = (uu___101_13558.sigtab);
              is_pattern = (uu___101_13558.is_pattern);
              instantiate_imp = (uu___101_13558.instantiate_imp);
              effects;
              generalize = (uu___101_13558.generalize);
              letrecs = (uu___101_13558.letrecs);
              top_level = (uu___101_13558.top_level);
              check_uvars = (uu___101_13558.check_uvars);
              use_eq = (uu___101_13558.use_eq);
              is_iface = (uu___101_13558.is_iface);
              admit = (uu___101_13558.admit);
              lax = (uu___101_13558.lax);
              lax_universes = (uu___101_13558.lax_universes);
              failhard = (uu___101_13558.failhard);
              nosynth = (uu___101_13558.nosynth);
              tc_term = (uu___101_13558.tc_term);
              type_of = (uu___101_13558.type_of);
              universe_of = (uu___101_13558.universe_of);
              check_type_of = (uu___101_13558.check_type_of);
              use_bv_sorts = (uu___101_13558.use_bv_sorts);
              qtbl_name_and_index = (uu___101_13558.qtbl_name_and_index);
              proof_ns = (uu___101_13558.proof_ns);
              synth_hook = (uu___101_13558.synth_hook);
              splice = (uu___101_13558.splice);
              is_native_tactic = (uu___101_13558.is_native_tactic);
              identifier_info = (uu___101_13558.identifier_info);
              tc_hooks = (uu___101_13558.tc_hooks);
              dsenv = (uu___101_13558.dsenv);
              dep_graph = (uu___101_13558.dep_graph)
            }))
      | uu____13559 -> env
  
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
        | uu____13583 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13591 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13591 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13608 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13608 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13626 =
                     let uu____13631 =
                       let uu____13632 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13637 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13644 =
                         let uu____13645 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13645  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13632 uu____13637 uu____13644
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13631)
                      in
                   FStar_Errors.raise_error uu____13626
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13650 =
                     let uu____13659 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13659 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13676  ->
                        fun uu____13677  ->
                          match (uu____13676, uu____13677) with
                          | ((x,uu____13699),(t,uu____13701)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13650
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13720 =
                     let uu___102_13721 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___102_13721.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___102_13721.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___102_13721.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___102_13721.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13720
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
          let uu____13743 = effect_decl_opt env effect_name  in
          match uu____13743 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13776 =
                only_reifiable &&
                  (let uu____13778 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13778)
                 in
              if uu____13776
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13794 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13813 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13842 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13842
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13843 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13843
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13853 =
                       let uu____13856 = get_range env  in
                       let uu____13857 =
                         let uu____13860 =
                           let uu____13861 =
                             let uu____13876 =
                               let uu____13879 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13879; wp]  in
                             (repr, uu____13876)  in
                           FStar_Syntax_Syntax.Tm_app uu____13861  in
                         FStar_Syntax_Syntax.mk uu____13860  in
                       uu____13857 FStar_Pervasives_Native.None uu____13856
                        in
                     FStar_Pervasives_Native.Some uu____13853)
  
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
          let uu____13925 =
            let uu____13930 =
              let uu____13931 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13931
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13930)  in
          let uu____13932 = get_range env  in
          FStar_Errors.raise_error uu____13925 uu____13932  in
        let uu____13933 = effect_repr_aux true env c u_c  in
        match uu____13933 with
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
      | uu____13967 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13974 =
        let uu____13975 = FStar_Syntax_Subst.compress t  in
        uu____13975.FStar_Syntax_Syntax.n  in
      match uu____13974 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13978,c) ->
          is_reifiable_comp env c
      | uu____13996 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____14018)::uu____14019 -> x :: rest
        | (Binding_sig_inst uu____14028)::uu____14029 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____14044 = push1 x rest1  in local :: uu____14044
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___103_14048 = env  in
       let uu____14049 = push1 s env.gamma  in
       {
         solver = (uu___103_14048.solver);
         range = (uu___103_14048.range);
         curmodule = (uu___103_14048.curmodule);
         gamma = uu____14049;
         gamma_cache = (uu___103_14048.gamma_cache);
         modules = (uu___103_14048.modules);
         expected_typ = (uu___103_14048.expected_typ);
         sigtab = (uu___103_14048.sigtab);
         is_pattern = (uu___103_14048.is_pattern);
         instantiate_imp = (uu___103_14048.instantiate_imp);
         effects = (uu___103_14048.effects);
         generalize = (uu___103_14048.generalize);
         letrecs = (uu___103_14048.letrecs);
         top_level = (uu___103_14048.top_level);
         check_uvars = (uu___103_14048.check_uvars);
         use_eq = (uu___103_14048.use_eq);
         is_iface = (uu___103_14048.is_iface);
         admit = (uu___103_14048.admit);
         lax = (uu___103_14048.lax);
         lax_universes = (uu___103_14048.lax_universes);
         failhard = (uu___103_14048.failhard);
         nosynth = (uu___103_14048.nosynth);
         tc_term = (uu___103_14048.tc_term);
         type_of = (uu___103_14048.type_of);
         universe_of = (uu___103_14048.universe_of);
         check_type_of = (uu___103_14048.check_type_of);
         use_bv_sorts = (uu___103_14048.use_bv_sorts);
         qtbl_name_and_index = (uu___103_14048.qtbl_name_and_index);
         proof_ns = (uu___103_14048.proof_ns);
         synth_hook = (uu___103_14048.synth_hook);
         splice = (uu___103_14048.splice);
         is_native_tactic = (uu___103_14048.is_native_tactic);
         identifier_info = (uu___103_14048.identifier_info);
         tc_hooks = (uu___103_14048.tc_hooks);
         dsenv = (uu___103_14048.dsenv);
         dep_graph = (uu___103_14048.dep_graph)
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
      let uu___104_14079 = env  in
      {
        solver = (uu___104_14079.solver);
        range = (uu___104_14079.range);
        curmodule = (uu___104_14079.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___104_14079.gamma_cache);
        modules = (uu___104_14079.modules);
        expected_typ = (uu___104_14079.expected_typ);
        sigtab = (uu___104_14079.sigtab);
        is_pattern = (uu___104_14079.is_pattern);
        instantiate_imp = (uu___104_14079.instantiate_imp);
        effects = (uu___104_14079.effects);
        generalize = (uu___104_14079.generalize);
        letrecs = (uu___104_14079.letrecs);
        top_level = (uu___104_14079.top_level);
        check_uvars = (uu___104_14079.check_uvars);
        use_eq = (uu___104_14079.use_eq);
        is_iface = (uu___104_14079.is_iface);
        admit = (uu___104_14079.admit);
        lax = (uu___104_14079.lax);
        lax_universes = (uu___104_14079.lax_universes);
        failhard = (uu___104_14079.failhard);
        nosynth = (uu___104_14079.nosynth);
        tc_term = (uu___104_14079.tc_term);
        type_of = (uu___104_14079.type_of);
        universe_of = (uu___104_14079.universe_of);
        check_type_of = (uu___104_14079.check_type_of);
        use_bv_sorts = (uu___104_14079.use_bv_sorts);
        qtbl_name_and_index = (uu___104_14079.qtbl_name_and_index);
        proof_ns = (uu___104_14079.proof_ns);
        synth_hook = (uu___104_14079.synth_hook);
        splice = (uu___104_14079.splice);
        is_native_tactic = (uu___104_14079.is_native_tactic);
        identifier_info = (uu___104_14079.identifier_info);
        tc_hooks = (uu___104_14079.tc_hooks);
        dsenv = (uu___104_14079.dsenv);
        dep_graph = (uu___104_14079.dep_graph)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
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
            (let uu___105_14124 = env  in
             {
               solver = (uu___105_14124.solver);
               range = (uu___105_14124.range);
               curmodule = (uu___105_14124.curmodule);
               gamma = rest;
               gamma_cache = (uu___105_14124.gamma_cache);
               modules = (uu___105_14124.modules);
               expected_typ = (uu___105_14124.expected_typ);
               sigtab = (uu___105_14124.sigtab);
               is_pattern = (uu___105_14124.is_pattern);
               instantiate_imp = (uu___105_14124.instantiate_imp);
               effects = (uu___105_14124.effects);
               generalize = (uu___105_14124.generalize);
               letrecs = (uu___105_14124.letrecs);
               top_level = (uu___105_14124.top_level);
               check_uvars = (uu___105_14124.check_uvars);
               use_eq = (uu___105_14124.use_eq);
               is_iface = (uu___105_14124.is_iface);
               admit = (uu___105_14124.admit);
               lax = (uu___105_14124.lax);
               lax_universes = (uu___105_14124.lax_universes);
               failhard = (uu___105_14124.failhard);
               nosynth = (uu___105_14124.nosynth);
               tc_term = (uu___105_14124.tc_term);
               type_of = (uu___105_14124.type_of);
               universe_of = (uu___105_14124.universe_of);
               check_type_of = (uu___105_14124.check_type_of);
               use_bv_sorts = (uu___105_14124.use_bv_sorts);
               qtbl_name_and_index = (uu___105_14124.qtbl_name_and_index);
               proof_ns = (uu___105_14124.proof_ns);
               synth_hook = (uu___105_14124.synth_hook);
               splice = (uu___105_14124.splice);
               is_native_tactic = (uu___105_14124.is_native_tactic);
               identifier_info = (uu___105_14124.identifier_info);
               tc_hooks = (uu___105_14124.tc_hooks);
               dsenv = (uu___105_14124.dsenv);
               dep_graph = (uu___105_14124.dep_graph)
             }))
    | uu____14125 -> FStar_Pervasives_Native.None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____14147  ->
             match uu____14147 with | (x,uu____14153) -> push_bv env1 x) env
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
            let uu___106_14181 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_14181.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_14181.FStar_Syntax_Syntax.index);
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
      (let uu___107_14211 = env  in
       {
         solver = (uu___107_14211.solver);
         range = (uu___107_14211.range);
         curmodule = (uu___107_14211.curmodule);
         gamma = [];
         gamma_cache = (uu___107_14211.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___107_14211.sigtab);
         is_pattern = (uu___107_14211.is_pattern);
         instantiate_imp = (uu___107_14211.instantiate_imp);
         effects = (uu___107_14211.effects);
         generalize = (uu___107_14211.generalize);
         letrecs = (uu___107_14211.letrecs);
         top_level = (uu___107_14211.top_level);
         check_uvars = (uu___107_14211.check_uvars);
         use_eq = (uu___107_14211.use_eq);
         is_iface = (uu___107_14211.is_iface);
         admit = (uu___107_14211.admit);
         lax = (uu___107_14211.lax);
         lax_universes = (uu___107_14211.lax_universes);
         failhard = (uu___107_14211.failhard);
         nosynth = (uu___107_14211.nosynth);
         tc_term = (uu___107_14211.tc_term);
         type_of = (uu___107_14211.type_of);
         universe_of = (uu___107_14211.universe_of);
         check_type_of = (uu___107_14211.check_type_of);
         use_bv_sorts = (uu___107_14211.use_bv_sorts);
         qtbl_name_and_index = (uu___107_14211.qtbl_name_and_index);
         proof_ns = (uu___107_14211.proof_ns);
         synth_hook = (uu___107_14211.synth_hook);
         splice = (uu___107_14211.splice);
         is_native_tactic = (uu___107_14211.is_native_tactic);
         identifier_info = (uu___107_14211.identifier_info);
         tc_hooks = (uu___107_14211.tc_hooks);
         dsenv = (uu___107_14211.dsenv);
         dep_graph = (uu___107_14211.dep_graph)
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
        let uu____14243 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____14243 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____14271 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____14271)
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___108_14284 = env  in
      {
        solver = (uu___108_14284.solver);
        range = (uu___108_14284.range);
        curmodule = (uu___108_14284.curmodule);
        gamma = (uu___108_14284.gamma);
        gamma_cache = (uu___108_14284.gamma_cache);
        modules = (uu___108_14284.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___108_14284.sigtab);
        is_pattern = (uu___108_14284.is_pattern);
        instantiate_imp = (uu___108_14284.instantiate_imp);
        effects = (uu___108_14284.effects);
        generalize = (uu___108_14284.generalize);
        letrecs = (uu___108_14284.letrecs);
        top_level = (uu___108_14284.top_level);
        check_uvars = (uu___108_14284.check_uvars);
        use_eq = false;
        is_iface = (uu___108_14284.is_iface);
        admit = (uu___108_14284.admit);
        lax = (uu___108_14284.lax);
        lax_universes = (uu___108_14284.lax_universes);
        failhard = (uu___108_14284.failhard);
        nosynth = (uu___108_14284.nosynth);
        tc_term = (uu___108_14284.tc_term);
        type_of = (uu___108_14284.type_of);
        universe_of = (uu___108_14284.universe_of);
        check_type_of = (uu___108_14284.check_type_of);
        use_bv_sorts = (uu___108_14284.use_bv_sorts);
        qtbl_name_and_index = (uu___108_14284.qtbl_name_and_index);
        proof_ns = (uu___108_14284.proof_ns);
        synth_hook = (uu___108_14284.synth_hook);
        splice = (uu___108_14284.splice);
        is_native_tactic = (uu___108_14284.is_native_tactic);
        identifier_info = (uu___108_14284.identifier_info);
        tc_hooks = (uu___108_14284.tc_hooks);
        dsenv = (uu___108_14284.dsenv);
        dep_graph = (uu___108_14284.dep_graph)
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
    let uu____14308 = expected_typ env_  in
    ((let uu___109_14314 = env_  in
      {
        solver = (uu___109_14314.solver);
        range = (uu___109_14314.range);
        curmodule = (uu___109_14314.curmodule);
        gamma = (uu___109_14314.gamma);
        gamma_cache = (uu___109_14314.gamma_cache);
        modules = (uu___109_14314.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___109_14314.sigtab);
        is_pattern = (uu___109_14314.is_pattern);
        instantiate_imp = (uu___109_14314.instantiate_imp);
        effects = (uu___109_14314.effects);
        generalize = (uu___109_14314.generalize);
        letrecs = (uu___109_14314.letrecs);
        top_level = (uu___109_14314.top_level);
        check_uvars = (uu___109_14314.check_uvars);
        use_eq = false;
        is_iface = (uu___109_14314.is_iface);
        admit = (uu___109_14314.admit);
        lax = (uu___109_14314.lax);
        lax_universes = (uu___109_14314.lax_universes);
        failhard = (uu___109_14314.failhard);
        nosynth = (uu___109_14314.nosynth);
        tc_term = (uu___109_14314.tc_term);
        type_of = (uu___109_14314.type_of);
        universe_of = (uu___109_14314.universe_of);
        check_type_of = (uu___109_14314.check_type_of);
        use_bv_sorts = (uu___109_14314.use_bv_sorts);
        qtbl_name_and_index = (uu___109_14314.qtbl_name_and_index);
        proof_ns = (uu___109_14314.proof_ns);
        synth_hook = (uu___109_14314.synth_hook);
        splice = (uu___109_14314.splice);
        is_native_tactic = (uu___109_14314.is_native_tactic);
        identifier_info = (uu___109_14314.identifier_info);
        tc_hooks = (uu___109_14314.tc_hooks);
        dsenv = (uu___109_14314.dsenv);
        dep_graph = (uu___109_14314.dep_graph)
      }), uu____14308)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid =
    let uu____14320 =
      let uu____14323 = FStar_Ident.id_of_text ""  in [uu____14323]  in
    FStar_Ident.lid_of_ids uu____14320  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____14329 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14329
        then
          let uu____14332 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___83_14342  ->
                    match uu___83_14342 with
                    | Binding_sig (uu____14345,se) -> [se]
                    | uu____14351 -> []))
             in
          FStar_All.pipe_right uu____14332 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___110_14358 = env  in
       {
         solver = (uu___110_14358.solver);
         range = (uu___110_14358.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___110_14358.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___110_14358.expected_typ);
         sigtab = (uu___110_14358.sigtab);
         is_pattern = (uu___110_14358.is_pattern);
         instantiate_imp = (uu___110_14358.instantiate_imp);
         effects = (uu___110_14358.effects);
         generalize = (uu___110_14358.generalize);
         letrecs = (uu___110_14358.letrecs);
         top_level = (uu___110_14358.top_level);
         check_uvars = (uu___110_14358.check_uvars);
         use_eq = (uu___110_14358.use_eq);
         is_iface = (uu___110_14358.is_iface);
         admit = (uu___110_14358.admit);
         lax = (uu___110_14358.lax);
         lax_universes = (uu___110_14358.lax_universes);
         failhard = (uu___110_14358.failhard);
         nosynth = (uu___110_14358.nosynth);
         tc_term = (uu___110_14358.tc_term);
         type_of = (uu___110_14358.type_of);
         universe_of = (uu___110_14358.universe_of);
         check_type_of = (uu___110_14358.check_type_of);
         use_bv_sorts = (uu___110_14358.use_bv_sorts);
         qtbl_name_and_index = (uu___110_14358.qtbl_name_and_index);
         proof_ns = (uu___110_14358.proof_ns);
         synth_hook = (uu___110_14358.synth_hook);
         splice = (uu___110_14358.splice);
         is_native_tactic = (uu___110_14358.is_native_tactic);
         identifier_info = (uu___110_14358.identifier_info);
         tc_hooks = (uu___110_14358.tc_hooks);
         dsenv = (uu___110_14358.dsenv);
         dep_graph = (uu___110_14358.dep_graph)
       })
  
let uvars_in_env : env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14439)::tl1 -> aux out tl1
      | (Binding_lid (uu____14443,(uu____14444,t)))::tl1 ->
          let uu____14459 =
            let uu____14466 = FStar_Syntax_Free.uvars t  in
            ext out uu____14466  in
          aux uu____14459 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14473;
            FStar_Syntax_Syntax.index = uu____14474;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14481 =
            let uu____14488 = FStar_Syntax_Free.uvars t  in
            ext out uu____14488  in
          aux uu____14481 tl1
      | (Binding_sig uu____14495)::uu____14496 -> out
      | (Binding_sig_inst uu____14505)::uu____14506 -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14561)::tl1 -> aux out tl1
      | (Binding_univ uu____14573)::tl1 -> aux out tl1
      | (Binding_lid (uu____14577,(uu____14578,t)))::tl1 ->
          let uu____14593 =
            let uu____14596 = FStar_Syntax_Free.univs t  in
            ext out uu____14596  in
          aux uu____14593 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14599;
            FStar_Syntax_Syntax.index = uu____14600;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14607 =
            let uu____14610 = FStar_Syntax_Free.univs t  in
            ext out uu____14610  in
          aux uu____14607 tl1
      | (Binding_sig uu____14613)::uu____14614 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14667)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14683 = FStar_Util.set_add uname out  in
          aux uu____14683 tl1
      | (Binding_lid (uu____14686,(uu____14687,t)))::tl1 ->
          let uu____14702 =
            let uu____14705 = FStar_Syntax_Free.univnames t  in
            ext out uu____14705  in
          aux uu____14702 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14708;
            FStar_Syntax_Syntax.index = uu____14709;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14716 =
            let uu____14719 = FStar_Syntax_Free.univnames t  in
            ext out uu____14719  in
          aux uu____14716 tl1
      | (Binding_sig uu____14722)::uu____14723 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___84_14747  ->
            match uu___84_14747 with
            | Binding_var x -> [x]
            | Binding_lid uu____14751 -> []
            | Binding_sig uu____14756 -> []
            | Binding_univ uu____14763 -> []
            | Binding_sig_inst uu____14764 -> []))
  
let binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14780 =
      let uu____14783 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14783
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14780 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____14805 =
      let uu____14806 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___85_14816  ->
                match uu___85_14816 with
                | Binding_var x ->
                    let uu____14818 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14818
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14821) ->
                    let uu____14822 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14822
                | Binding_sig (ls,uu____14824) ->
                    let uu____14829 =
                      let uu____14830 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14830
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14829
                | Binding_sig_inst (ls,uu____14840,uu____14841) ->
                    let uu____14846 =
                      let uu____14847 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14847
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14846))
         in
      FStar_All.pipe_right uu____14806 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14805 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14864 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14864
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14892  ->
                 fun uu____14893  ->
                   match (uu____14892, uu____14893) with
                   | ((b1,uu____14911),(b2,uu____14913)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let string_of_delta_level : delta_level -> Prims.string =
  fun uu___86_14955  ->
    match uu___86_14955 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14956 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___87_14974  ->
             match uu___87_14974 with
             | Binding_sig (lids,uu____14980) -> FStar_List.append lids keys
             | uu____14985 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14991  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let should_enc_path : env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____15025) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____15044,uu____15045) -> false  in
      let uu____15054 =
        FStar_List.tryFind
          (fun uu____15072  ->
             match uu____15072 with | (p,uu____15080) -> list_prefix p path)
          env.proof_ns
         in
      match uu____15054 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____15091,b) -> b
  
let should_enc_lid : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____15109 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____15109
  
let cons_proof_ns : Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___111_15121 = e  in
        {
          solver = (uu___111_15121.solver);
          range = (uu___111_15121.range);
          curmodule = (uu___111_15121.curmodule);
          gamma = (uu___111_15121.gamma);
          gamma_cache = (uu___111_15121.gamma_cache);
          modules = (uu___111_15121.modules);
          expected_typ = (uu___111_15121.expected_typ);
          sigtab = (uu___111_15121.sigtab);
          is_pattern = (uu___111_15121.is_pattern);
          instantiate_imp = (uu___111_15121.instantiate_imp);
          effects = (uu___111_15121.effects);
          generalize = (uu___111_15121.generalize);
          letrecs = (uu___111_15121.letrecs);
          top_level = (uu___111_15121.top_level);
          check_uvars = (uu___111_15121.check_uvars);
          use_eq = (uu___111_15121.use_eq);
          is_iface = (uu___111_15121.is_iface);
          admit = (uu___111_15121.admit);
          lax = (uu___111_15121.lax);
          lax_universes = (uu___111_15121.lax_universes);
          failhard = (uu___111_15121.failhard);
          nosynth = (uu___111_15121.nosynth);
          tc_term = (uu___111_15121.tc_term);
          type_of = (uu___111_15121.type_of);
          universe_of = (uu___111_15121.universe_of);
          check_type_of = (uu___111_15121.check_type_of);
          use_bv_sorts = (uu___111_15121.use_bv_sorts);
          qtbl_name_and_index = (uu___111_15121.qtbl_name_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___111_15121.synth_hook);
          splice = (uu___111_15121.splice);
          is_native_tactic = (uu___111_15121.is_native_tactic);
          identifier_info = (uu___111_15121.identifier_info);
          tc_hooks = (uu___111_15121.tc_hooks);
          dsenv = (uu___111_15121.dsenv);
          dep_graph = (uu___111_15121.dep_graph)
        }
  
let add_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path 
let rem_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path 
let get_proof_ns : env -> proof_namespace = fun e  -> e.proof_ns 
let set_proof_ns : proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___112_15147 = e  in
      {
        solver = (uu___112_15147.solver);
        range = (uu___112_15147.range);
        curmodule = (uu___112_15147.curmodule);
        gamma = (uu___112_15147.gamma);
        gamma_cache = (uu___112_15147.gamma_cache);
        modules = (uu___112_15147.modules);
        expected_typ = (uu___112_15147.expected_typ);
        sigtab = (uu___112_15147.sigtab);
        is_pattern = (uu___112_15147.is_pattern);
        instantiate_imp = (uu___112_15147.instantiate_imp);
        effects = (uu___112_15147.effects);
        generalize = (uu___112_15147.generalize);
        letrecs = (uu___112_15147.letrecs);
        top_level = (uu___112_15147.top_level);
        check_uvars = (uu___112_15147.check_uvars);
        use_eq = (uu___112_15147.use_eq);
        is_iface = (uu___112_15147.is_iface);
        admit = (uu___112_15147.admit);
        lax = (uu___112_15147.lax);
        lax_universes = (uu___112_15147.lax_universes);
        failhard = (uu___112_15147.failhard);
        nosynth = (uu___112_15147.nosynth);
        tc_term = (uu___112_15147.tc_term);
        type_of = (uu___112_15147.type_of);
        universe_of = (uu___112_15147.universe_of);
        check_type_of = (uu___112_15147.check_type_of);
        use_bv_sorts = (uu___112_15147.use_bv_sorts);
        qtbl_name_and_index = (uu___112_15147.qtbl_name_and_index);
        proof_ns = ns;
        synth_hook = (uu___112_15147.synth_hook);
        splice = (uu___112_15147.splice);
        is_native_tactic = (uu___112_15147.is_native_tactic);
        identifier_info = (uu___112_15147.identifier_info);
        tc_hooks = (uu___112_15147.tc_hooks);
        dsenv = (uu___112_15147.dsenv);
        dep_graph = (uu___112_15147.dep_graph)
      }
  
let unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____15158 = FStar_Syntax_Free.names t  in
      let uu____15161 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____15158 uu____15161
  
let closed : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____15178 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____15178
  
let closed' : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____15184 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____15184
  
let string_of_proof_ns : env -> Prims.string =
  fun env  ->
    let aux uu____15199 =
      match uu____15199 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____15215 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____15215)
       in
    let uu____15217 =
      let uu____15220 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____15220 FStar_List.rev  in
    FStar_All.pipe_right uu____15217 (FStar_String.concat " ")
  
let dummy_solver : solver_t =
  {
    init = (fun uu____15237  -> ());
    push = (fun uu____15239  -> ());
    pop = (fun uu____15241  -> ());
    encode_modul = (fun uu____15244  -> fun uu____15245  -> ());
    encode_sig = (fun uu____15248  -> fun uu____15249  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____15255 =
             let uu____15262 = FStar_Options.peek ()  in (e, g, uu____15262)
              in
           [uu____15255]);
    solve = (fun uu____15278  -> fun uu____15279  -> fun uu____15280  -> ());
    finish = (fun uu____15286  -> ());
    refresh = (fun uu____15288  -> ())
  } 
let mk_copy : env -> env =
  fun en  ->
    let uu___113_15292 = en  in
    let uu____15293 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____15296 = FStar_Util.smap_copy en.sigtab  in
    let uu____15299 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___113_15292.solver);
      range = (uu___113_15292.range);
      curmodule = (uu___113_15292.curmodule);
      gamma = (uu___113_15292.gamma);
      gamma_cache = uu____15293;
      modules = (uu___113_15292.modules);
      expected_typ = (uu___113_15292.expected_typ);
      sigtab = uu____15296;
      is_pattern = (uu___113_15292.is_pattern);
      instantiate_imp = (uu___113_15292.instantiate_imp);
      effects = (uu___113_15292.effects);
      generalize = (uu___113_15292.generalize);
      letrecs = (uu___113_15292.letrecs);
      top_level = (uu___113_15292.top_level);
      check_uvars = (uu___113_15292.check_uvars);
      use_eq = (uu___113_15292.use_eq);
      is_iface = (uu___113_15292.is_iface);
      admit = (uu___113_15292.admit);
      lax = (uu___113_15292.lax);
      lax_universes = (uu___113_15292.lax_universes);
      failhard = (uu___113_15292.failhard);
      nosynth = (uu___113_15292.nosynth);
      tc_term = (uu___113_15292.tc_term);
      type_of = (uu___113_15292.type_of);
      universe_of = (uu___113_15292.universe_of);
      check_type_of = (uu___113_15292.check_type_of);
      use_bv_sorts = (uu___113_15292.use_bv_sorts);
      qtbl_name_and_index = (uu___113_15292.qtbl_name_and_index);
      proof_ns = (uu___113_15292.proof_ns);
      synth_hook = (uu___113_15292.synth_hook);
      splice = (uu___113_15292.splice);
      is_native_tactic = (uu___113_15292.is_native_tactic);
      identifier_info = (uu___113_15292.identifier_info);
      tc_hooks = (uu___113_15292.tc_hooks);
      dsenv = uu____15299;
      dep_graph = (uu___113_15292.dep_graph)
    }
  