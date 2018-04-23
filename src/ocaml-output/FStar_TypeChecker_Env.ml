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
    match projectee with | Binding_var _0 -> true | uu____50 -> false
  
let __proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_lid : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____68 -> false
  
let __proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let uu___is_Binding_sig : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____100 -> false
  
let __proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let uu___is_Binding_univ : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____132 -> false
  
let __proj__Binding_univ__item___0 : binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let uu___is_Binding_sig_inst : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____154 -> false
  
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
    match projectee with | NoDelta  -> true | uu____196 -> false
  
let uu___is_Inlining : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____202 -> false
  
let uu___is_Eager_unfolding_only : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____208 -> false
  
let uu___is_Unfold : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____215 -> false
  
let __proj__Unfold__item___0 : delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0 
let uu___is_UnfoldTac : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____228 -> false
  
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
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
    }[@@deriving show]
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> unit }[@@deriving show]
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qtbl_name_and_index
  
let __proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap =
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
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__normalized_eff_names
  
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
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
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
  
let __proj__Mksolver_t__item__init : solver_t -> env -> unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let __proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let __proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let __proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let __proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit =
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
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let __proj__Mksolver_t__item__finish : solver_t -> unit -> unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let __proj__Mksolver_t__item__refresh : solver_t -> unit -> unit =
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
  tcenv_hooks -> env -> binding -> unit =
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
           (fun uu___73_7467  ->
              match uu___73_7467 with
              | Binding_var x ->
                  let y =
                    let uu____7470 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____7470  in
                  let uu____7471 =
                    let uu____7472 = FStar_Syntax_Subst.compress y  in
                    uu____7472.FStar_Syntax_Syntax.n  in
                  (match uu____7471 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____7476 =
                         let uu___88_7477 = y1  in
                         let uu____7478 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___88_7477.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___88_7477.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____7478
                         }  in
                       Binding_var uu____7476
                   | uu____7481 -> failwith "Not a renaming")
              | b -> b))
  
let rename_env : FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___89_7493 = env  in
      let uu____7494 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___89_7493.solver);
        range = (uu___89_7493.range);
        curmodule = (uu___89_7493.curmodule);
        gamma = uu____7494;
        gamma_cache = (uu___89_7493.gamma_cache);
        modules = (uu___89_7493.modules);
        expected_typ = (uu___89_7493.expected_typ);
        sigtab = (uu___89_7493.sigtab);
        is_pattern = (uu___89_7493.is_pattern);
        instantiate_imp = (uu___89_7493.instantiate_imp);
        effects = (uu___89_7493.effects);
        generalize = (uu___89_7493.generalize);
        letrecs = (uu___89_7493.letrecs);
        top_level = (uu___89_7493.top_level);
        check_uvars = (uu___89_7493.check_uvars);
        use_eq = (uu___89_7493.use_eq);
        is_iface = (uu___89_7493.is_iface);
        admit = (uu___89_7493.admit);
        lax = (uu___89_7493.lax);
        lax_universes = (uu___89_7493.lax_universes);
        failhard = (uu___89_7493.failhard);
        nosynth = (uu___89_7493.nosynth);
        tc_term = (uu___89_7493.tc_term);
        type_of = (uu___89_7493.type_of);
        universe_of = (uu___89_7493.universe_of);
        check_type_of = (uu___89_7493.check_type_of);
        use_bv_sorts = (uu___89_7493.use_bv_sorts);
        qtbl_name_and_index = (uu___89_7493.qtbl_name_and_index);
        normalized_eff_names = (uu___89_7493.normalized_eff_names);
        proof_ns = (uu___89_7493.proof_ns);
        synth_hook = (uu___89_7493.synth_hook);
        splice = (uu___89_7493.splice);
        is_native_tactic = (uu___89_7493.is_native_tactic);
        identifier_info = (uu___89_7493.identifier_info);
        tc_hooks = (uu___89_7493.tc_hooks);
        dsenv = (uu___89_7493.dsenv);
        dep_graph = (uu___89_7493.dep_graph)
      }
  
let default_tc_hooks : tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____7501  -> fun uu____7502  -> ()) } 
let tc_hooks : env -> tcenv_hooks = fun env  -> env.tc_hooks 
let set_tc_hooks : env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___90_7518 = env  in
      {
        solver = (uu___90_7518.solver);
        range = (uu___90_7518.range);
        curmodule = (uu___90_7518.curmodule);
        gamma = (uu___90_7518.gamma);
        gamma_cache = (uu___90_7518.gamma_cache);
        modules = (uu___90_7518.modules);
        expected_typ = (uu___90_7518.expected_typ);
        sigtab = (uu___90_7518.sigtab);
        is_pattern = (uu___90_7518.is_pattern);
        instantiate_imp = (uu___90_7518.instantiate_imp);
        effects = (uu___90_7518.effects);
        generalize = (uu___90_7518.generalize);
        letrecs = (uu___90_7518.letrecs);
        top_level = (uu___90_7518.top_level);
        check_uvars = (uu___90_7518.check_uvars);
        use_eq = (uu___90_7518.use_eq);
        is_iface = (uu___90_7518.is_iface);
        admit = (uu___90_7518.admit);
        lax = (uu___90_7518.lax);
        lax_universes = (uu___90_7518.lax_universes);
        failhard = (uu___90_7518.failhard);
        nosynth = (uu___90_7518.nosynth);
        tc_term = (uu___90_7518.tc_term);
        type_of = (uu___90_7518.type_of);
        universe_of = (uu___90_7518.universe_of);
        check_type_of = (uu___90_7518.check_type_of);
        use_bv_sorts = (uu___90_7518.use_bv_sorts);
        qtbl_name_and_index = (uu___90_7518.qtbl_name_and_index);
        normalized_eff_names = (uu___90_7518.normalized_eff_names);
        proof_ns = (uu___90_7518.proof_ns);
        synth_hook = (uu___90_7518.synth_hook);
        splice = (uu___90_7518.splice);
        is_native_tactic = (uu___90_7518.is_native_tactic);
        identifier_info = (uu___90_7518.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___90_7518.dsenv);
        dep_graph = (uu___90_7518.dep_graph)
      }
  
let set_dep_graph : env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___91_7529 = e  in
      {
        solver = (uu___91_7529.solver);
        range = (uu___91_7529.range);
        curmodule = (uu___91_7529.curmodule);
        gamma = (uu___91_7529.gamma);
        gamma_cache = (uu___91_7529.gamma_cache);
        modules = (uu___91_7529.modules);
        expected_typ = (uu___91_7529.expected_typ);
        sigtab = (uu___91_7529.sigtab);
        is_pattern = (uu___91_7529.is_pattern);
        instantiate_imp = (uu___91_7529.instantiate_imp);
        effects = (uu___91_7529.effects);
        generalize = (uu___91_7529.generalize);
        letrecs = (uu___91_7529.letrecs);
        top_level = (uu___91_7529.top_level);
        check_uvars = (uu___91_7529.check_uvars);
        use_eq = (uu___91_7529.use_eq);
        is_iface = (uu___91_7529.is_iface);
        admit = (uu___91_7529.admit);
        lax = (uu___91_7529.lax);
        lax_universes = (uu___91_7529.lax_universes);
        failhard = (uu___91_7529.failhard);
        nosynth = (uu___91_7529.nosynth);
        tc_term = (uu___91_7529.tc_term);
        type_of = (uu___91_7529.type_of);
        universe_of = (uu___91_7529.universe_of);
        check_type_of = (uu___91_7529.check_type_of);
        use_bv_sorts = (uu___91_7529.use_bv_sorts);
        qtbl_name_and_index = (uu___91_7529.qtbl_name_and_index);
        normalized_eff_names = (uu___91_7529.normalized_eff_names);
        proof_ns = (uu___91_7529.proof_ns);
        synth_hook = (uu___91_7529.synth_hook);
        splice = (uu___91_7529.splice);
        is_native_tactic = (uu___91_7529.is_native_tactic);
        identifier_info = (uu___91_7529.identifier_info);
        tc_hooks = (uu___91_7529.tc_hooks);
        dsenv = (uu___91_7529.dsenv);
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
      | (NoDelta ,uu____7552) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____7553,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____7554,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____7555 -> false
  
let default_table_size : Prims.int = (Prims.lift_native_int (200)) 
let new_sigtab : 'Auu____7564 . unit -> 'Auu____7564 FStar_Util.smap =
  fun uu____7571  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____7576 . unit -> 'Auu____7576 FStar_Util.smap =
  fun uu____7583  -> FStar_Util.smap_create (Prims.lift_native_int (100)) 
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
                let uu____7693 = new_gamma_cache ()  in
                let uu____7696 = new_sigtab ()  in
                let uu____7699 =
                  let uu____7712 =
                    FStar_Util.smap_create (Prims.lift_native_int (10))  in
                  (uu____7712, FStar_Pervasives_Native.None)  in
                let uu____7727 =
                  FStar_Util.smap_create (Prims.lift_native_int (20))  in
                let uu____7730 = FStar_Options.using_facts_from ()  in
                let uu____7731 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____7734 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____7693;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____7696;
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
                  qtbl_name_and_index = uu____7699;
                  normalized_eff_names = uu____7727;
                  proof_ns = uu____7730;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____7770  -> false);
                  identifier_info = uu____7731;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____7734;
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
let push_query_indices : unit -> unit =
  fun uu____7861  ->
    let uu____7862 = FStar_ST.op_Bang query_indices  in
    match uu____7862 with
    | [] -> failwith "Empty query indices!"
    | uu____7916 ->
        let uu____7925 =
          let uu____7934 =
            let uu____7941 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____7941  in
          let uu____7995 = FStar_ST.op_Bang query_indices  in uu____7934 ::
            uu____7995
           in
        FStar_ST.op_Colon_Equals query_indices uu____7925
  
let pop_query_indices : unit -> unit =
  fun uu____8092  ->
    let uu____8093 = FStar_ST.op_Bang query_indices  in
    match uu____8093 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit =
  fun uu____8216  ->
    match uu____8216 with
    | (l,n1) ->
        let uu____8223 = FStar_ST.op_Bang query_indices  in
        (match uu____8223 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____8342 -> failwith "Empty query indices")
  
let peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____8361  ->
    let uu____8362 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____8362
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____8439 =
       let uu____8442 = FStar_ST.op_Bang stack  in env :: uu____8442  in
     FStar_ST.op_Colon_Equals stack uu____8439);
    (let uu___92_8499 = env  in
     let uu____8500 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____8503 = FStar_Util.smap_copy (sigtab env)  in
     let uu____8506 =
       let uu____8519 =
         let uu____8522 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____8522  in
       let uu____8547 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____8519, uu____8547)  in
     let uu____8588 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____8591 =
       let uu____8594 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____8594  in
     {
       solver = (uu___92_8499.solver);
       range = (uu___92_8499.range);
       curmodule = (uu___92_8499.curmodule);
       gamma = (uu___92_8499.gamma);
       gamma_cache = uu____8500;
       modules = (uu___92_8499.modules);
       expected_typ = (uu___92_8499.expected_typ);
       sigtab = uu____8503;
       is_pattern = (uu___92_8499.is_pattern);
       instantiate_imp = (uu___92_8499.instantiate_imp);
       effects = (uu___92_8499.effects);
       generalize = (uu___92_8499.generalize);
       letrecs = (uu___92_8499.letrecs);
       top_level = (uu___92_8499.top_level);
       check_uvars = (uu___92_8499.check_uvars);
       use_eq = (uu___92_8499.use_eq);
       is_iface = (uu___92_8499.is_iface);
       admit = (uu___92_8499.admit);
       lax = (uu___92_8499.lax);
       lax_universes = (uu___92_8499.lax_universes);
       failhard = (uu___92_8499.failhard);
       nosynth = (uu___92_8499.nosynth);
       tc_term = (uu___92_8499.tc_term);
       type_of = (uu___92_8499.type_of);
       universe_of = (uu___92_8499.universe_of);
       check_type_of = (uu___92_8499.check_type_of);
       use_bv_sorts = (uu___92_8499.use_bv_sorts);
       qtbl_name_and_index = uu____8506;
       normalized_eff_names = uu____8588;
       proof_ns = (uu___92_8499.proof_ns);
       synth_hook = (uu___92_8499.synth_hook);
       splice = (uu___92_8499.splice);
       is_native_tactic = (uu___92_8499.is_native_tactic);
       identifier_info = uu____8591;
       tc_hooks = (uu___92_8499.tc_hooks);
       dsenv = (uu___92_8499.dsenv);
       dep_graph = (uu___92_8499.dep_graph)
     })
  
let pop_stack : unit -> env =
  fun uu____8644  ->
    let uu____8645 = FStar_ST.op_Bang stack  in
    match uu____8645 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____8707 -> failwith "Impossible: Too many pops"
  
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
    | (uu____8746,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____8778 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____8804  ->
                  match uu____8804 with
                  | (m,uu____8810) -> FStar_Ident.lid_equals l m))
           in
        (match uu____8778 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.lift_native_int (1))  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___93_8818 = env  in
               {
                 solver = (uu___93_8818.solver);
                 range = (uu___93_8818.range);
                 curmodule = (uu___93_8818.curmodule);
                 gamma = (uu___93_8818.gamma);
                 gamma_cache = (uu___93_8818.gamma_cache);
                 modules = (uu___93_8818.modules);
                 expected_typ = (uu___93_8818.expected_typ);
                 sigtab = (uu___93_8818.sigtab);
                 is_pattern = (uu___93_8818.is_pattern);
                 instantiate_imp = (uu___93_8818.instantiate_imp);
                 effects = (uu___93_8818.effects);
                 generalize = (uu___93_8818.generalize);
                 letrecs = (uu___93_8818.letrecs);
                 top_level = (uu___93_8818.top_level);
                 check_uvars = (uu___93_8818.check_uvars);
                 use_eq = (uu___93_8818.use_eq);
                 is_iface = (uu___93_8818.is_iface);
                 admit = (uu___93_8818.admit);
                 lax = (uu___93_8818.lax);
                 lax_universes = (uu___93_8818.lax_universes);
                 failhard = (uu___93_8818.failhard);
                 nosynth = (uu___93_8818.nosynth);
                 tc_term = (uu___93_8818.tc_term);
                 type_of = (uu___93_8818.type_of);
                 universe_of = (uu___93_8818.universe_of);
                 check_type_of = (uu___93_8818.check_type_of);
                 use_bv_sorts = (uu___93_8818.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___93_8818.normalized_eff_names);
                 proof_ns = (uu___93_8818.proof_ns);
                 synth_hook = (uu___93_8818.synth_hook);
                 splice = (uu___93_8818.splice);
                 is_native_tactic = (uu___93_8818.is_native_tactic);
                 identifier_info = (uu___93_8818.identifier_info);
                 tc_hooks = (uu___93_8818.tc_hooks);
                 dsenv = (uu___93_8818.dsenv);
                 dep_graph = (uu___93_8818.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____8831,m) ->
             let next = m + (Prims.lift_native_int (1))  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___94_8840 = env  in
               {
                 solver = (uu___94_8840.solver);
                 range = (uu___94_8840.range);
                 curmodule = (uu___94_8840.curmodule);
                 gamma = (uu___94_8840.gamma);
                 gamma_cache = (uu___94_8840.gamma_cache);
                 modules = (uu___94_8840.modules);
                 expected_typ = (uu___94_8840.expected_typ);
                 sigtab = (uu___94_8840.sigtab);
                 is_pattern = (uu___94_8840.is_pattern);
                 instantiate_imp = (uu___94_8840.instantiate_imp);
                 effects = (uu___94_8840.effects);
                 generalize = (uu___94_8840.generalize);
                 letrecs = (uu___94_8840.letrecs);
                 top_level = (uu___94_8840.top_level);
                 check_uvars = (uu___94_8840.check_uvars);
                 use_eq = (uu___94_8840.use_eq);
                 is_iface = (uu___94_8840.is_iface);
                 admit = (uu___94_8840.admit);
                 lax = (uu___94_8840.lax);
                 lax_universes = (uu___94_8840.lax_universes);
                 failhard = (uu___94_8840.failhard);
                 nosynth = (uu___94_8840.nosynth);
                 tc_term = (uu___94_8840.tc_term);
                 type_of = (uu___94_8840.type_of);
                 universe_of = (uu___94_8840.universe_of);
                 check_type_of = (uu___94_8840.check_type_of);
                 use_bv_sorts = (uu___94_8840.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___94_8840.normalized_eff_names);
                 proof_ns = (uu___94_8840.proof_ns);
                 synth_hook = (uu___94_8840.synth_hook);
                 splice = (uu___94_8840.splice);
                 is_native_tactic = (uu___94_8840.is_native_tactic);
                 identifier_info = (uu___94_8840.identifier_info);
                 tc_hooks = (uu___94_8840.tc_hooks);
                 dsenv = (uu___94_8840.dsenv);
                 dep_graph = (uu___94_8840.dep_graph)
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
        (let uu___95_8874 = e  in
         {
           solver = (uu___95_8874.solver);
           range = r;
           curmodule = (uu___95_8874.curmodule);
           gamma = (uu___95_8874.gamma);
           gamma_cache = (uu___95_8874.gamma_cache);
           modules = (uu___95_8874.modules);
           expected_typ = (uu___95_8874.expected_typ);
           sigtab = (uu___95_8874.sigtab);
           is_pattern = (uu___95_8874.is_pattern);
           instantiate_imp = (uu___95_8874.instantiate_imp);
           effects = (uu___95_8874.effects);
           generalize = (uu___95_8874.generalize);
           letrecs = (uu___95_8874.letrecs);
           top_level = (uu___95_8874.top_level);
           check_uvars = (uu___95_8874.check_uvars);
           use_eq = (uu___95_8874.use_eq);
           is_iface = (uu___95_8874.is_iface);
           admit = (uu___95_8874.admit);
           lax = (uu___95_8874.lax);
           lax_universes = (uu___95_8874.lax_universes);
           failhard = (uu___95_8874.failhard);
           nosynth = (uu___95_8874.nosynth);
           tc_term = (uu___95_8874.tc_term);
           type_of = (uu___95_8874.type_of);
           universe_of = (uu___95_8874.universe_of);
           check_type_of = (uu___95_8874.check_type_of);
           use_bv_sorts = (uu___95_8874.use_bv_sorts);
           qtbl_name_and_index = (uu___95_8874.qtbl_name_and_index);
           normalized_eff_names = (uu___95_8874.normalized_eff_names);
           proof_ns = (uu___95_8874.proof_ns);
           synth_hook = (uu___95_8874.synth_hook);
           splice = (uu___95_8874.splice);
           is_native_tactic = (uu___95_8874.is_native_tactic);
           identifier_info = (uu___95_8874.identifier_info);
           tc_hooks = (uu___95_8874.tc_hooks);
           dsenv = (uu___95_8874.dsenv);
           dep_graph = (uu___95_8874.dep_graph)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let toggle_id_info : env -> Prims.bool -> unit =
  fun env  ->
    fun enabled  ->
      let uu____8890 =
        let uu____8891 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____8891 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____8890
  
let insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____8953 =
          let uu____8954 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____8954 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____8953
  
let insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____9016 =
          let uu____9017 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____9017 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9016
  
let promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit =
  fun env  ->
    fun ty_map  ->
      let uu____9079 =
        let uu____9080 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____9080 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9079
  
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___96_9149 = env  in
      {
        solver = (uu___96_9149.solver);
        range = (uu___96_9149.range);
        curmodule = lid;
        gamma = (uu___96_9149.gamma);
        gamma_cache = (uu___96_9149.gamma_cache);
        modules = (uu___96_9149.modules);
        expected_typ = (uu___96_9149.expected_typ);
        sigtab = (uu___96_9149.sigtab);
        is_pattern = (uu___96_9149.is_pattern);
        instantiate_imp = (uu___96_9149.instantiate_imp);
        effects = (uu___96_9149.effects);
        generalize = (uu___96_9149.generalize);
        letrecs = (uu___96_9149.letrecs);
        top_level = (uu___96_9149.top_level);
        check_uvars = (uu___96_9149.check_uvars);
        use_eq = (uu___96_9149.use_eq);
        is_iface = (uu___96_9149.is_iface);
        admit = (uu___96_9149.admit);
        lax = (uu___96_9149.lax);
        lax_universes = (uu___96_9149.lax_universes);
        failhard = (uu___96_9149.failhard);
        nosynth = (uu___96_9149.nosynth);
        tc_term = (uu___96_9149.tc_term);
        type_of = (uu___96_9149.type_of);
        universe_of = (uu___96_9149.universe_of);
        check_type_of = (uu___96_9149.check_type_of);
        use_bv_sorts = (uu___96_9149.use_bv_sorts);
        qtbl_name_and_index = (uu___96_9149.qtbl_name_and_index);
        normalized_eff_names = (uu___96_9149.normalized_eff_names);
        proof_ns = (uu___96_9149.proof_ns);
        synth_hook = (uu___96_9149.synth_hook);
        splice = (uu___96_9149.splice);
        is_native_tactic = (uu___96_9149.is_native_tactic);
        identifier_info = (uu___96_9149.identifier_info);
        tc_hooks = (uu___96_9149.tc_hooks);
        dsenv = (uu___96_9149.dsenv);
        dep_graph = (uu___96_9149.dep_graph)
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
      let uu____9176 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____9176
  
let name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____9186 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____9186)
  
let variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____9196 =
      let uu____9197 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____9197  in
    (FStar_Errors.Fatal_VariableNotFound, uu____9196)
  
let new_u_univ : unit -> FStar_Syntax_Syntax.universe =
  fun uu____9202  ->
    let uu____9203 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____9203
  
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
      | ((formals,t),uu____9245) ->
          let n1 = (FStar_List.length formals) - (Prims.lift_native_int (1))
             in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____9267 = FStar_Syntax_Subst.subst vs t  in (us, uu____9267)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___74_9283  ->
    match uu___74_9283 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____9307  -> new_u_univ ()))
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
      let uu____9324 = inst_tscheme t  in
      match uu____9324 with
      | (us,t1) ->
          let uu____9335 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____9335)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____9355  ->
          match uu____9355 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____9370 =
                         let uu____9371 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____9372 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____9373 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____9374 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____9371 uu____9372 uu____9373 uu____9374
                          in
                       failwith uu____9370)
                    else ();
                    (let uu____9376 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____9376))
               | uu____9383 ->
                   let uu____9384 =
                     let uu____9385 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____9385
                      in
                   failwith uu____9384)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____9391 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____9397 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____9403 -> false
  
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
             | ([],uu____9445) -> Maybe
             | (uu____9452,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____9471 -> No  in
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
          let uu____9562 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____9562 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___75_9608  ->
                   match uu___75_9608 with
                   | Binding_lid (l,t) ->
                       let uu____9631 = FStar_Ident.lid_equals lid l  in
                       if uu____9631
                       then
                         let uu____9652 =
                           let uu____9671 =
                             let uu____9686 = inst_tscheme t  in
                             FStar_Util.Inl uu____9686  in
                           let uu____9701 = FStar_Ident.range_of_lid l  in
                           (uu____9671, uu____9701)  in
                         FStar_Pervasives_Native.Some uu____9652
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____9753,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____9755);
                                     FStar_Syntax_Syntax.sigrng = uu____9756;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____9757;
                                     FStar_Syntax_Syntax.sigmeta = uu____9758;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____9759;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____9779 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____9779
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____9827 ->
                             FStar_Pervasives_Native.Some t
                         | uu____9834 -> cache t  in
                       let uu____9835 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____9835 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____9877 =
                              let uu____9878 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                uu____9878)
                               in
                            maybe_cache uu____9877)
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____9912 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____9912 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____9954 =
                              let uu____9973 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                uu____9973)
                               in
                            FStar_Pervasives_Native.Some uu____9954)
                   | uu____10018 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____10078 = find_in_sigtab env lid  in
         match uu____10078 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10165) ->
          add_sigelts env ses
      | uu____10174 ->
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
            | uu____10188 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit =
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
        (fun uu___76_10219  ->
           match uu___76_10219 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____10237 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____10298,lb::[]),uu____10300) ->
            let uu____10313 =
              let uu____10322 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____10331 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____10322, uu____10331)  in
            FStar_Pervasives_Native.Some uu____10313
        | FStar_Syntax_Syntax.Sig_let ((uu____10344,lbs),uu____10346) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____10382 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____10394 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____10394
                     then
                       let uu____10405 =
                         let uu____10414 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____10423 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____10414, uu____10423)  in
                       FStar_Pervasives_Native.Some uu____10405
                     else FStar_Pervasives_Native.None)
        | uu____10445 -> FStar_Pervasives_Native.None
  
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
          let uu____10504 =
            let uu____10513 =
              let uu____10518 =
                let uu____10519 =
                  let uu____10522 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____10522
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____10519)  in
              inst_tscheme1 uu____10518  in
            (uu____10513, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____10504
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____10542,uu____10543) ->
          let uu____10548 =
            let uu____10557 =
              let uu____10562 =
                let uu____10563 =
                  let uu____10566 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____10566  in
                (us, uu____10563)  in
              inst_tscheme1 uu____10562  in
            (uu____10557, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____10548
      | uu____10583 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____10671 =
          match uu____10671 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____10767,uvs,t,uu____10770,uu____10771,uu____10772);
                      FStar_Syntax_Syntax.sigrng = uu____10773;
                      FStar_Syntax_Syntax.sigquals = uu____10774;
                      FStar_Syntax_Syntax.sigmeta = uu____10775;
                      FStar_Syntax_Syntax.sigattrs = uu____10776;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____10797 =
                     let uu____10806 = inst_tscheme1 (uvs, t)  in
                     (uu____10806, rng)  in
                   FStar_Pervasives_Native.Some uu____10797
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____10826;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____10828;
                      FStar_Syntax_Syntax.sigattrs = uu____10829;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____10846 =
                     let uu____10847 = in_cur_mod env l  in uu____10847 = Yes
                      in
                   if uu____10846
                   then
                     let uu____10858 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____10858
                      then
                        let uu____10871 =
                          let uu____10880 = inst_tscheme1 (uvs, t)  in
                          (uu____10880, rng)  in
                        FStar_Pervasives_Native.Some uu____10871
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10907 =
                        let uu____10916 = inst_tscheme1 (uvs, t)  in
                        (uu____10916, rng)  in
                      FStar_Pervasives_Native.Some uu____10907)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____10937,uu____10938);
                      FStar_Syntax_Syntax.sigrng = uu____10939;
                      FStar_Syntax_Syntax.sigquals = uu____10940;
                      FStar_Syntax_Syntax.sigmeta = uu____10941;
                      FStar_Syntax_Syntax.sigattrs = uu____10942;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____10981 =
                          let uu____10990 = inst_tscheme1 (uvs, k)  in
                          (uu____10990, rng)  in
                        FStar_Pervasives_Native.Some uu____10981
                    | uu____11007 ->
                        let uu____11008 =
                          let uu____11017 =
                            let uu____11022 =
                              let uu____11023 =
                                let uu____11026 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11026
                                 in
                              (uvs, uu____11023)  in
                            inst_tscheme1 uu____11022  in
                          (uu____11017, rng)  in
                        FStar_Pervasives_Native.Some uu____11008)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11047,uu____11048);
                      FStar_Syntax_Syntax.sigrng = uu____11049;
                      FStar_Syntax_Syntax.sigquals = uu____11050;
                      FStar_Syntax_Syntax.sigmeta = uu____11051;
                      FStar_Syntax_Syntax.sigattrs = uu____11052;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____11092 =
                          let uu____11101 = inst_tscheme_with (uvs, k) us  in
                          (uu____11101, rng)  in
                        FStar_Pervasives_Native.Some uu____11092
                    | uu____11118 ->
                        let uu____11119 =
                          let uu____11128 =
                            let uu____11133 =
                              let uu____11134 =
                                let uu____11137 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11137
                                 in
                              (uvs, uu____11134)  in
                            inst_tscheme_with uu____11133 us  in
                          (uu____11128, rng)  in
                        FStar_Pervasives_Native.Some uu____11119)
               | FStar_Util.Inr se ->
                   let uu____11171 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____11192;
                          FStar_Syntax_Syntax.sigrng = uu____11193;
                          FStar_Syntax_Syntax.sigquals = uu____11194;
                          FStar_Syntax_Syntax.sigmeta = uu____11195;
                          FStar_Syntax_Syntax.sigattrs = uu____11196;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____11211 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____11171
                     (FStar_Util.map_option
                        (fun uu____11259  ->
                           match uu____11259 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____11290 =
          let uu____11301 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____11301 mapper  in
        match uu____11290 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____11375 =
              let uu____11386 =
                let uu____11393 =
                  let uu___97_11396 = t  in
                  let uu____11397 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___97_11396.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____11397;
                    FStar_Syntax_Syntax.vars =
                      (uu___97_11396.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____11393)  in
              (uu____11386, r)  in
            FStar_Pervasives_Native.Some uu____11375
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11444 = lookup_qname env l  in
      match uu____11444 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____11463 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____11515 = try_lookup_bv env bv  in
      match uu____11515 with
      | FStar_Pervasives_Native.None  ->
          let uu____11530 = variable_not_found bv  in
          FStar_Errors.raise_error uu____11530 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____11545 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____11546 =
            let uu____11547 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____11547  in
          (uu____11545, uu____11546)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____11568 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____11568 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____11634 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____11634  in
          let uu____11635 =
            let uu____11644 =
              let uu____11649 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____11649)  in
            (uu____11644, r1)  in
          FStar_Pervasives_Native.Some uu____11635
  
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
        let uu____11683 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____11683 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____11716,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____11741 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____11741  in
            let uu____11742 =
              let uu____11747 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____11747, r1)  in
            FStar_Pervasives_Native.Some uu____11742
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____11770 = try_lookup_lid env l  in
      match uu____11770 with
      | FStar_Pervasives_Native.None  ->
          let uu____11797 = name_not_found l  in
          let uu____11802 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____11797 uu____11802
      | FStar_Pervasives_Native.Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___77_11842  ->
              match uu___77_11842 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____11844 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____11863 = lookup_qname env lid  in
      match uu____11863 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11872,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____11875;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11877;
              FStar_Syntax_Syntax.sigattrs = uu____11878;_},FStar_Pervasives_Native.None
            ),uu____11879)
          ->
          let uu____11928 =
            let uu____11939 =
              let uu____11944 =
                let uu____11945 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____11945 t  in
              (uvs, uu____11944)  in
            (uu____11939, q)  in
          FStar_Pervasives_Native.Some uu____11928
      | uu____11962 -> FStar_Pervasives_Native.None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____11983 = lookup_qname env lid  in
      match uu____11983 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11988,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____11991;
              FStar_Syntax_Syntax.sigquals = uu____11992;
              FStar_Syntax_Syntax.sigmeta = uu____11993;
              FStar_Syntax_Syntax.sigattrs = uu____11994;_},FStar_Pervasives_Native.None
            ),uu____11995)
          ->
          let uu____12044 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12044 (uvs, t)
      | uu____12045 ->
          let uu____12046 = name_not_found lid  in
          let uu____12051 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12046 uu____12051
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____12070 = lookup_qname env lid  in
      match uu____12070 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12075,uvs,t,uu____12078,uu____12079,uu____12080);
              FStar_Syntax_Syntax.sigrng = uu____12081;
              FStar_Syntax_Syntax.sigquals = uu____12082;
              FStar_Syntax_Syntax.sigmeta = uu____12083;
              FStar_Syntax_Syntax.sigattrs = uu____12084;_},FStar_Pervasives_Native.None
            ),uu____12085)
          ->
          let uu____12138 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12138 (uvs, t)
      | uu____12139 ->
          let uu____12140 = name_not_found lid  in
          let uu____12145 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12140 uu____12145
  
let datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____12166 = lookup_qname env lid  in
      match uu____12166 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12173,uu____12174,uu____12175,uu____12176,uu____12177,dcs);
              FStar_Syntax_Syntax.sigrng = uu____12179;
              FStar_Syntax_Syntax.sigquals = uu____12180;
              FStar_Syntax_Syntax.sigmeta = uu____12181;
              FStar_Syntax_Syntax.sigattrs = uu____12182;_},uu____12183),uu____12184)
          -> (true, dcs)
      | uu____12245 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____12258 = lookup_qname env lid  in
      match uu____12258 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12259,uu____12260,uu____12261,l,uu____12263,uu____12264);
              FStar_Syntax_Syntax.sigrng = uu____12265;
              FStar_Syntax_Syntax.sigquals = uu____12266;
              FStar_Syntax_Syntax.sigmeta = uu____12267;
              FStar_Syntax_Syntax.sigattrs = uu____12268;_},uu____12269),uu____12270)
          -> l
      | uu____12325 ->
          let uu____12326 =
            let uu____12327 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____12327  in
          failwith uu____12326
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____12376)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____12427,lbs),uu____12429)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____12457 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____12457
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____12489 -> FStar_Pervasives_Native.None)
        | uu____12494 -> FStar_Pervasives_Native.None
  
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
        let uu____12524 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____12524
  
let attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____12549),uu____12550) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____12599 -> FStar_Pervasives_Native.None
  
let lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____12620 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____12620
  
let try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____12639 = lookup_qname env ftv  in
      match uu____12639 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____12643) ->
          let uu____12688 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____12688 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____12709,t),r) ->
               let uu____12724 =
                 let uu____12725 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____12725 t  in
               FStar_Pervasives_Native.Some uu____12724)
      | uu____12726 -> FStar_Pervasives_Native.None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____12737 = try_lookup_effect_lid env ftv  in
      match uu____12737 with
      | FStar_Pervasives_Native.None  ->
          let uu____12740 = name_not_found ftv  in
          let uu____12745 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____12740 uu____12745
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
        let uu____12768 = lookup_qname env lid0  in
        match uu____12768 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____12779);
                FStar_Syntax_Syntax.sigrng = uu____12780;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____12782;
                FStar_Syntax_Syntax.sigattrs = uu____12783;_},FStar_Pervasives_Native.None
              ),uu____12784)
            ->
            let lid1 =
              let uu____12838 =
                let uu____12839 = FStar_Ident.range_of_lid lid  in
                let uu____12840 =
                  let uu____12841 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____12841  in
                FStar_Range.set_use_range uu____12839 uu____12840  in
              FStar_Ident.set_lid_range lid uu____12838  in
            let uu____12842 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___78_12846  ->
                      match uu___78_12846 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12847 -> false))
               in
            if uu____12842
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____12861 =
                      let uu____12862 =
                        let uu____12863 = get_range env  in
                        FStar_Range.string_of_range uu____12863  in
                      let uu____12864 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____12865 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____12862 uu____12864 uu____12865
                       in
                    failwith uu____12861)
                  in
               match (binders, univs1) with
               | ([],uu____12872) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____12889,uu____12890::uu____12891::uu____12892) ->
                   let uu____12897 =
                     let uu____12898 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____12899 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____12898 uu____12899
                      in
                   failwith uu____12897
               | uu____12906 ->
                   let uu____12911 =
                     let uu____12916 =
                       let uu____12917 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____12917)  in
                     inst_tscheme_with uu____12916 insts  in
                   (match uu____12911 with
                    | (uu____12928,t) ->
                        let t1 =
                          let uu____12931 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____12931 t  in
                        let uu____12932 =
                          let uu____12933 = FStar_Syntax_Subst.compress t1
                             in
                          uu____12933.FStar_Syntax_Syntax.n  in
                        (match uu____12932 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____12980 -> failwith "Impossible")))
        | uu____12987 -> FStar_Pervasives_Native.None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____13010 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____13010 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____13023,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____13030 = find1 l2  in
            (match uu____13030 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____13037 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____13037 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____13041 = find1 l  in
            (match uu____13041 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____13046 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____13046
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____13060 = lookup_qname env l1  in
      match uu____13060 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____13063;
              FStar_Syntax_Syntax.sigrng = uu____13064;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13066;
              FStar_Syntax_Syntax.sigattrs = uu____13067;_},uu____13068),uu____13069)
          -> q
      | uu____13120 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____13141 =
          let uu____13142 =
            let uu____13143 = FStar_Util.string_of_int i  in
            let uu____13144 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____13143 uu____13144
             in
          failwith uu____13142  in
        let uu____13145 = lookup_datacon env lid  in
        match uu____13145 with
        | (uu____13150,t) ->
            let uu____13152 =
              let uu____13153 = FStar_Syntax_Subst.compress t  in
              uu____13153.FStar_Syntax_Syntax.n  in
            (match uu____13152 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____13157) ->
                 if
                   (i < (Prims.lift_native_int (0))) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____13188 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____13188
                      FStar_Pervasives_Native.fst)
             | uu____13197 -> fail1 ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____13208 = lookup_qname env l  in
      match uu____13208 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13209,uu____13210,uu____13211);
              FStar_Syntax_Syntax.sigrng = uu____13212;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13214;
              FStar_Syntax_Syntax.sigattrs = uu____13215;_},uu____13216),uu____13217)
          ->
          FStar_Util.for_some
            (fun uu___79_13270  ->
               match uu___79_13270 with
               | FStar_Syntax_Syntax.Projector uu____13271 -> true
               | uu____13276 -> false) quals
      | uu____13277 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13288 = lookup_qname env lid  in
      match uu____13288 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13289,uu____13290,uu____13291,uu____13292,uu____13293,uu____13294);
              FStar_Syntax_Syntax.sigrng = uu____13295;
              FStar_Syntax_Syntax.sigquals = uu____13296;
              FStar_Syntax_Syntax.sigmeta = uu____13297;
              FStar_Syntax_Syntax.sigattrs = uu____13298;_},uu____13299),uu____13300)
          -> true
      | uu____13355 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13366 = lookup_qname env lid  in
      match uu____13366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13367,uu____13368,uu____13369,uu____13370,uu____13371,uu____13372);
              FStar_Syntax_Syntax.sigrng = uu____13373;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13375;
              FStar_Syntax_Syntax.sigattrs = uu____13376;_},uu____13377),uu____13378)
          ->
          FStar_Util.for_some
            (fun uu___80_13439  ->
               match uu___80_13439 with
               | FStar_Syntax_Syntax.RecordType uu____13440 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____13449 -> true
               | uu____13458 -> false) quals
      | uu____13459 -> false
  
let qninfo_is_action : qninfo -> Prims.bool =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____13465,uu____13466);
            FStar_Syntax_Syntax.sigrng = uu____13467;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____13469;
            FStar_Syntax_Syntax.sigattrs = uu____13470;_},uu____13471),uu____13472)
        ->
        FStar_Util.for_some
          (fun uu___81_13529  ->
             match uu___81_13529 with
             | FStar_Syntax_Syntax.Action uu____13530 -> true
             | uu____13531 -> false) quals
    | uu____13532 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13543 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____13543
  
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
      let uu____13557 =
        let uu____13558 = FStar_Syntax_Util.un_uinst head1  in
        uu____13558.FStar_Syntax_Syntax.n  in
      match uu____13557 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____13562 -> false
  
let is_irreducible : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____13573 = lookup_qname env l  in
      match uu____13573 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____13575),uu____13576) ->
          FStar_Util.for_some
            (fun uu___82_13624  ->
               match uu___82_13624 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____13625 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____13626 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____13697 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____13713) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____13730 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____13737 ->
                 FStar_Pervasives_Native.Some true
             | uu____13754 -> FStar_Pervasives_Native.Some false)
         in
      let uu____13755 =
        let uu____13758 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____13758 mapper  in
      match uu____13755 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____13808 = lookup_qname env lid  in
      match uu____13808 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13809,uu____13810,tps,uu____13812,uu____13813,uu____13814);
              FStar_Syntax_Syntax.sigrng = uu____13815;
              FStar_Syntax_Syntax.sigquals = uu____13816;
              FStar_Syntax_Syntax.sigmeta = uu____13817;
              FStar_Syntax_Syntax.sigattrs = uu____13818;_},uu____13819),uu____13820)
          -> FStar_List.length tps
      | uu____13883 ->
          let uu____13884 = name_not_found lid  in
          let uu____13889 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13884 uu____13889
  
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
           (fun uu____13933  ->
              match uu____13933 with
              | (d,uu____13941) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____13956 = effect_decl_opt env l  in
      match uu____13956 with
      | FStar_Pervasives_Native.None  ->
          let uu____13971 = name_not_found l  in
          let uu____13976 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13971 uu____13976
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let identity_mlift : mlift =
  {
    mlift_wp = (fun uu____13998  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____14017  ->
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
        let uu____14048 = FStar_Ident.lid_equals l1 l2  in
        if uu____14048
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____14056 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____14056
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____14064 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____14117  ->
                        match uu____14117 with
                        | (m1,m2,uu____14130,uu____14131,uu____14132) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____14064 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14149 =
                    let uu____14154 =
                      let uu____14155 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____14156 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____14155
                        uu____14156
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____14154)
                     in
                  FStar_Errors.raise_error uu____14149 env.range
              | FStar_Pervasives_Native.Some
                  (uu____14163,uu____14164,m3,j1,j2) -> (m3, j1, j2)))
  
let monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____14197 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____14197
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
  'Auu____14213 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____14213)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____14242 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____14268  ->
                match uu____14268 with
                | (d,uu____14274) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____14242 with
      | FStar_Pervasives_Native.None  ->
          let uu____14285 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____14285
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____14298 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____14298 with
           | (uu____14309,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____14319)::(wp,uu____14321)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____14357 -> failwith "Impossible"))
  
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
          let uu____14404 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____14404
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____14406 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____14406
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
                  let uu____14414 = get_range env  in
                  let uu____14415 =
                    let uu____14422 =
                      let uu____14423 =
                        let uu____14438 =
                          let uu____14441 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____14441]  in
                        (null_wp, uu____14438)  in
                      FStar_Syntax_Syntax.Tm_app uu____14423  in
                    FStar_Syntax_Syntax.mk uu____14422  in
                  uu____14415 FStar_Pervasives_Native.None uu____14414  in
                let uu____14447 =
                  let uu____14448 =
                    let uu____14457 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____14457]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____14448;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____14447))
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___98_14470 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___98_14470.order);
              joins = (uu___98_14470.joins)
            }  in
          let uu___99_14479 = env  in
          {
            solver = (uu___99_14479.solver);
            range = (uu___99_14479.range);
            curmodule = (uu___99_14479.curmodule);
            gamma = (uu___99_14479.gamma);
            gamma_cache = (uu___99_14479.gamma_cache);
            modules = (uu___99_14479.modules);
            expected_typ = (uu___99_14479.expected_typ);
            sigtab = (uu___99_14479.sigtab);
            is_pattern = (uu___99_14479.is_pattern);
            instantiate_imp = (uu___99_14479.instantiate_imp);
            effects;
            generalize = (uu___99_14479.generalize);
            letrecs = (uu___99_14479.letrecs);
            top_level = (uu___99_14479.top_level);
            check_uvars = (uu___99_14479.check_uvars);
            use_eq = (uu___99_14479.use_eq);
            is_iface = (uu___99_14479.is_iface);
            admit = (uu___99_14479.admit);
            lax = (uu___99_14479.lax);
            lax_universes = (uu___99_14479.lax_universes);
            failhard = (uu___99_14479.failhard);
            nosynth = (uu___99_14479.nosynth);
            tc_term = (uu___99_14479.tc_term);
            type_of = (uu___99_14479.type_of);
            universe_of = (uu___99_14479.universe_of);
            check_type_of = (uu___99_14479.check_type_of);
            use_bv_sorts = (uu___99_14479.use_bv_sorts);
            qtbl_name_and_index = (uu___99_14479.qtbl_name_and_index);
            normalized_eff_names = (uu___99_14479.normalized_eff_names);
            proof_ns = (uu___99_14479.proof_ns);
            synth_hook = (uu___99_14479.synth_hook);
            splice = (uu___99_14479.splice);
            is_native_tactic = (uu___99_14479.is_native_tactic);
            identifier_info = (uu___99_14479.identifier_info);
            tc_hooks = (uu___99_14479.tc_hooks);
            dsenv = (uu___99_14479.dsenv);
            dep_graph = (uu___99_14479.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____14509 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____14509  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____14667 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____14668 = l1 u t wp e  in
                                l2 u t uu____14667 uu____14668))
                | uu____14669 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____14737 = inst_tscheme_with lift_t [u]  in
            match uu____14737 with
            | (uu____14744,lift_t1) ->
                let uu____14746 =
                  let uu____14753 =
                    let uu____14754 =
                      let uu____14769 =
                        let uu____14772 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____14773 =
                          let uu____14776 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____14776]  in
                        uu____14772 :: uu____14773  in
                      (lift_t1, uu____14769)  in
                    FStar_Syntax_Syntax.Tm_app uu____14754  in
                  FStar_Syntax_Syntax.mk uu____14753  in
                uu____14746 FStar_Pervasives_Native.None
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
            let uu____14848 = inst_tscheme_with lift_t [u]  in
            match uu____14848 with
            | (uu____14855,lift_t1) ->
                let uu____14857 =
                  let uu____14864 =
                    let uu____14865 =
                      let uu____14880 =
                        let uu____14883 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____14884 =
                          let uu____14887 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____14888 =
                            let uu____14891 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____14891]  in
                          uu____14887 :: uu____14888  in
                        uu____14883 :: uu____14884  in
                      (lift_t1, uu____14880)  in
                    FStar_Syntax_Syntax.Tm_app uu____14865  in
                  FStar_Syntax_Syntax.mk uu____14864  in
                uu____14857 FStar_Pervasives_Native.None
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
              let uu____14947 =
                let uu____14948 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____14948
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____14947  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____14952 =
              let uu____14953 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____14953  in
            let uu____14954 =
              let uu____14955 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____14981 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____14981)
                 in
              FStar_Util.dflt "none" uu____14955  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____14952
              uu____14954
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____15007  ->
                    match uu____15007 with
                    | (e,uu____15015) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____15038 =
            match uu____15038 with
            | (i,j) ->
                let uu____15049 = FStar_Ident.lid_equals i j  in
                if uu____15049
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____15081 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____15091 = FStar_Ident.lid_equals i k  in
                        if uu____15091
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____15102 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____15102
                                  then []
                                  else
                                    (let uu____15106 =
                                       let uu____15115 =
                                         find_edge order1 (i, k)  in
                                       let uu____15118 =
                                         find_edge order1 (k, j)  in
                                       (uu____15115, uu____15118)  in
                                     match uu____15106 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____15133 =
                                           compose_edges e1 e2  in
                                         [uu____15133]
                                     | uu____15134 -> [])))))
                 in
              FStar_List.append order1 uu____15081  in
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
                   let uu____15164 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____15166 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____15166
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____15164
                   then
                     let uu____15171 =
                       let uu____15176 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____15176)
                        in
                     let uu____15177 = get_range env  in
                     FStar_Errors.raise_error uu____15171 uu____15177
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____15254 = FStar_Ident.lid_equals i j
                                   in
                                if uu____15254
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____15303 =
                                              let uu____15312 =
                                                find_edge order2 (i, k)  in
                                              let uu____15315 =
                                                find_edge order2 (j, k)  in
                                              (uu____15312, uu____15315)  in
                                            match uu____15303 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____15357,uu____15358)
                                                     ->
                                                     let uu____15365 =
                                                       let uu____15370 =
                                                         let uu____15371 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____15371
                                                          in
                                                       let uu____15374 =
                                                         let uu____15375 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____15375
                                                          in
                                                       (uu____15370,
                                                         uu____15374)
                                                        in
                                                     (match uu____15365 with
                                                      | (true ,true ) ->
                                                          let uu____15386 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____15386
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
                                            | uu____15411 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___100_15484 = env.effects  in
              { decls = (uu___100_15484.decls); order = order2; joins }  in
            let uu___101_15485 = env  in
            {
              solver = (uu___101_15485.solver);
              range = (uu___101_15485.range);
              curmodule = (uu___101_15485.curmodule);
              gamma = (uu___101_15485.gamma);
              gamma_cache = (uu___101_15485.gamma_cache);
              modules = (uu___101_15485.modules);
              expected_typ = (uu___101_15485.expected_typ);
              sigtab = (uu___101_15485.sigtab);
              is_pattern = (uu___101_15485.is_pattern);
              instantiate_imp = (uu___101_15485.instantiate_imp);
              effects;
              generalize = (uu___101_15485.generalize);
              letrecs = (uu___101_15485.letrecs);
              top_level = (uu___101_15485.top_level);
              check_uvars = (uu___101_15485.check_uvars);
              use_eq = (uu___101_15485.use_eq);
              is_iface = (uu___101_15485.is_iface);
              admit = (uu___101_15485.admit);
              lax = (uu___101_15485.lax);
              lax_universes = (uu___101_15485.lax_universes);
              failhard = (uu___101_15485.failhard);
              nosynth = (uu___101_15485.nosynth);
              tc_term = (uu___101_15485.tc_term);
              type_of = (uu___101_15485.type_of);
              universe_of = (uu___101_15485.universe_of);
              check_type_of = (uu___101_15485.check_type_of);
              use_bv_sorts = (uu___101_15485.use_bv_sorts);
              qtbl_name_and_index = (uu___101_15485.qtbl_name_and_index);
              normalized_eff_names = (uu___101_15485.normalized_eff_names);
              proof_ns = (uu___101_15485.proof_ns);
              synth_hook = (uu___101_15485.synth_hook);
              splice = (uu___101_15485.splice);
              is_native_tactic = (uu___101_15485.is_native_tactic);
              identifier_info = (uu___101_15485.identifier_info);
              tc_hooks = (uu___101_15485.tc_hooks);
              dsenv = (uu___101_15485.dsenv);
              dep_graph = (uu___101_15485.dep_graph)
            }))
      | uu____15486 -> env
  
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
        | uu____15514 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____15526 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____15526 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____15543 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____15543 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.lift_native_int (1)))
                then
                  (let uu____15561 =
                     let uu____15566 =
                       let uu____15567 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____15572 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.lift_native_int (1)))
                          in
                       let uu____15579 =
                         let uu____15580 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____15580  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____15567 uu____15572 uu____15579
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____15566)
                      in
                   FStar_Errors.raise_error uu____15561
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____15585 =
                     let uu____15594 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____15594 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____15611  ->
                        fun uu____15612  ->
                          match (uu____15611, uu____15612) with
                          | ((x,uu____15634),(t,uu____15636)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____15585
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____15655 =
                     let uu___102_15656 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___102_15656.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___102_15656.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___102_15656.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___102_15656.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____15655
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
          let uu____15686 = effect_decl_opt env effect_name  in
          match uu____15686 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____15719 =
                only_reifiable &&
                  (let uu____15721 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____15721)
                 in
              if uu____15719
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____15737 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____15756 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____15785 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____15785
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____15786 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____15786
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____15796 =
                       let uu____15799 = get_range env  in
                       let uu____15800 =
                         let uu____15807 =
                           let uu____15808 =
                             let uu____15823 =
                               let uu____15826 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____15826; wp]  in
                             (repr, uu____15823)  in
                           FStar_Syntax_Syntax.Tm_app uu____15808  in
                         FStar_Syntax_Syntax.mk uu____15807  in
                       uu____15800 FStar_Pervasives_Native.None uu____15799
                        in
                     FStar_Pervasives_Native.Some uu____15796)
  
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
          let uu____15886 =
            let uu____15891 =
              let uu____15892 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____15892
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____15891)  in
          let uu____15893 = get_range env  in
          FStar_Errors.raise_error uu____15886 uu____15893  in
        let uu____15894 = effect_repr_aux true env c u_c  in
        match uu____15894 with
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
      | uu____15940 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____15951 =
        let uu____15952 = FStar_Syntax_Subst.compress t  in
        uu____15952.FStar_Syntax_Syntax.n  in
      match uu____15951 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____15955,c) ->
          is_reifiable_comp env c
      | uu____15973 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____16003)::uu____16004 -> x :: rest
        | (Binding_sig_inst uu____16013)::uu____16014 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____16029 = push1 x rest1  in local :: uu____16029
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___103_16033 = env  in
       let uu____16034 = push1 s env.gamma  in
       {
         solver = (uu___103_16033.solver);
         range = (uu___103_16033.range);
         curmodule = (uu___103_16033.curmodule);
         gamma = uu____16034;
         gamma_cache = (uu___103_16033.gamma_cache);
         modules = (uu___103_16033.modules);
         expected_typ = (uu___103_16033.expected_typ);
         sigtab = (uu___103_16033.sigtab);
         is_pattern = (uu___103_16033.is_pattern);
         instantiate_imp = (uu___103_16033.instantiate_imp);
         effects = (uu___103_16033.effects);
         generalize = (uu___103_16033.generalize);
         letrecs = (uu___103_16033.letrecs);
         top_level = (uu___103_16033.top_level);
         check_uvars = (uu___103_16033.check_uvars);
         use_eq = (uu___103_16033.use_eq);
         is_iface = (uu___103_16033.is_iface);
         admit = (uu___103_16033.admit);
         lax = (uu___103_16033.lax);
         lax_universes = (uu___103_16033.lax_universes);
         failhard = (uu___103_16033.failhard);
         nosynth = (uu___103_16033.nosynth);
         tc_term = (uu___103_16033.tc_term);
         type_of = (uu___103_16033.type_of);
         universe_of = (uu___103_16033.universe_of);
         check_type_of = (uu___103_16033.check_type_of);
         use_bv_sorts = (uu___103_16033.use_bv_sorts);
         qtbl_name_and_index = (uu___103_16033.qtbl_name_and_index);
         normalized_eff_names = (uu___103_16033.normalized_eff_names);
         proof_ns = (uu___103_16033.proof_ns);
         synth_hook = (uu___103_16033.synth_hook);
         splice = (uu___103_16033.splice);
         is_native_tactic = (uu___103_16033.is_native_tactic);
         identifier_info = (uu___103_16033.identifier_info);
         tc_hooks = (uu___103_16033.tc_hooks);
         dsenv = (uu___103_16033.dsenv);
         dep_graph = (uu___103_16033.dep_graph)
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
      let uu___104_16078 = env  in
      {
        solver = (uu___104_16078.solver);
        range = (uu___104_16078.range);
        curmodule = (uu___104_16078.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___104_16078.gamma_cache);
        modules = (uu___104_16078.modules);
        expected_typ = (uu___104_16078.expected_typ);
        sigtab = (uu___104_16078.sigtab);
        is_pattern = (uu___104_16078.is_pattern);
        instantiate_imp = (uu___104_16078.instantiate_imp);
        effects = (uu___104_16078.effects);
        generalize = (uu___104_16078.generalize);
        letrecs = (uu___104_16078.letrecs);
        top_level = (uu___104_16078.top_level);
        check_uvars = (uu___104_16078.check_uvars);
        use_eq = (uu___104_16078.use_eq);
        is_iface = (uu___104_16078.is_iface);
        admit = (uu___104_16078.admit);
        lax = (uu___104_16078.lax);
        lax_universes = (uu___104_16078.lax_universes);
        failhard = (uu___104_16078.failhard);
        nosynth = (uu___104_16078.nosynth);
        tc_term = (uu___104_16078.tc_term);
        type_of = (uu___104_16078.type_of);
        universe_of = (uu___104_16078.universe_of);
        check_type_of = (uu___104_16078.check_type_of);
        use_bv_sorts = (uu___104_16078.use_bv_sorts);
        qtbl_name_and_index = (uu___104_16078.qtbl_name_and_index);
        normalized_eff_names = (uu___104_16078.normalized_eff_names);
        proof_ns = (uu___104_16078.proof_ns);
        synth_hook = (uu___104_16078.synth_hook);
        splice = (uu___104_16078.splice);
        is_native_tactic = (uu___104_16078.is_native_tactic);
        identifier_info = (uu___104_16078.identifier_info);
        tc_hooks = (uu___104_16078.tc_hooks);
        dsenv = (uu___104_16078.dsenv);
        dep_graph = (uu___104_16078.dep_graph)
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
            (let uu___105_16133 = env  in
             {
               solver = (uu___105_16133.solver);
               range = (uu___105_16133.range);
               curmodule = (uu___105_16133.curmodule);
               gamma = rest;
               gamma_cache = (uu___105_16133.gamma_cache);
               modules = (uu___105_16133.modules);
               expected_typ = (uu___105_16133.expected_typ);
               sigtab = (uu___105_16133.sigtab);
               is_pattern = (uu___105_16133.is_pattern);
               instantiate_imp = (uu___105_16133.instantiate_imp);
               effects = (uu___105_16133.effects);
               generalize = (uu___105_16133.generalize);
               letrecs = (uu___105_16133.letrecs);
               top_level = (uu___105_16133.top_level);
               check_uvars = (uu___105_16133.check_uvars);
               use_eq = (uu___105_16133.use_eq);
               is_iface = (uu___105_16133.is_iface);
               admit = (uu___105_16133.admit);
               lax = (uu___105_16133.lax);
               lax_universes = (uu___105_16133.lax_universes);
               failhard = (uu___105_16133.failhard);
               nosynth = (uu___105_16133.nosynth);
               tc_term = (uu___105_16133.tc_term);
               type_of = (uu___105_16133.type_of);
               universe_of = (uu___105_16133.universe_of);
               check_type_of = (uu___105_16133.check_type_of);
               use_bv_sorts = (uu___105_16133.use_bv_sorts);
               qtbl_name_and_index = (uu___105_16133.qtbl_name_and_index);
               normalized_eff_names = (uu___105_16133.normalized_eff_names);
               proof_ns = (uu___105_16133.proof_ns);
               synth_hook = (uu___105_16133.synth_hook);
               splice = (uu___105_16133.splice);
               is_native_tactic = (uu___105_16133.is_native_tactic);
               identifier_info = (uu___105_16133.identifier_info);
               tc_hooks = (uu___105_16133.tc_hooks);
               dsenv = (uu___105_16133.dsenv);
               dep_graph = (uu___105_16133.dep_graph)
             }))
    | uu____16134 -> FStar_Pervasives_Native.None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____16160  ->
             match uu____16160 with | (x,uu____16166) -> push_bv env1 x) env
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
            let uu___106_16196 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_16196.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_16196.FStar_Syntax_Syntax.index);
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
      (let uu___107_16236 = env  in
       {
         solver = (uu___107_16236.solver);
         range = (uu___107_16236.range);
         curmodule = (uu___107_16236.curmodule);
         gamma = [];
         gamma_cache = (uu___107_16236.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___107_16236.sigtab);
         is_pattern = (uu___107_16236.is_pattern);
         instantiate_imp = (uu___107_16236.instantiate_imp);
         effects = (uu___107_16236.effects);
         generalize = (uu___107_16236.generalize);
         letrecs = (uu___107_16236.letrecs);
         top_level = (uu___107_16236.top_level);
         check_uvars = (uu___107_16236.check_uvars);
         use_eq = (uu___107_16236.use_eq);
         is_iface = (uu___107_16236.is_iface);
         admit = (uu___107_16236.admit);
         lax = (uu___107_16236.lax);
         lax_universes = (uu___107_16236.lax_universes);
         failhard = (uu___107_16236.failhard);
         nosynth = (uu___107_16236.nosynth);
         tc_term = (uu___107_16236.tc_term);
         type_of = (uu___107_16236.type_of);
         universe_of = (uu___107_16236.universe_of);
         check_type_of = (uu___107_16236.check_type_of);
         use_bv_sorts = (uu___107_16236.use_bv_sorts);
         qtbl_name_and_index = (uu___107_16236.qtbl_name_and_index);
         normalized_eff_names = (uu___107_16236.normalized_eff_names);
         proof_ns = (uu___107_16236.proof_ns);
         synth_hook = (uu___107_16236.synth_hook);
         splice = (uu___107_16236.splice);
         is_native_tactic = (uu___107_16236.is_native_tactic);
         identifier_info = (uu___107_16236.identifier_info);
         tc_hooks = (uu___107_16236.tc_hooks);
         dsenv = (uu___107_16236.dsenv);
         dep_graph = (uu___107_16236.dep_graph)
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
        let uu____16278 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____16278 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____16306 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____16306)
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___108_16323 = env  in
      {
        solver = (uu___108_16323.solver);
        range = (uu___108_16323.range);
        curmodule = (uu___108_16323.curmodule);
        gamma = (uu___108_16323.gamma);
        gamma_cache = (uu___108_16323.gamma_cache);
        modules = (uu___108_16323.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___108_16323.sigtab);
        is_pattern = (uu___108_16323.is_pattern);
        instantiate_imp = (uu___108_16323.instantiate_imp);
        effects = (uu___108_16323.effects);
        generalize = (uu___108_16323.generalize);
        letrecs = (uu___108_16323.letrecs);
        top_level = (uu___108_16323.top_level);
        check_uvars = (uu___108_16323.check_uvars);
        use_eq = false;
        is_iface = (uu___108_16323.is_iface);
        admit = (uu___108_16323.admit);
        lax = (uu___108_16323.lax);
        lax_universes = (uu___108_16323.lax_universes);
        failhard = (uu___108_16323.failhard);
        nosynth = (uu___108_16323.nosynth);
        tc_term = (uu___108_16323.tc_term);
        type_of = (uu___108_16323.type_of);
        universe_of = (uu___108_16323.universe_of);
        check_type_of = (uu___108_16323.check_type_of);
        use_bv_sorts = (uu___108_16323.use_bv_sorts);
        qtbl_name_and_index = (uu___108_16323.qtbl_name_and_index);
        normalized_eff_names = (uu___108_16323.normalized_eff_names);
        proof_ns = (uu___108_16323.proof_ns);
        synth_hook = (uu___108_16323.synth_hook);
        splice = (uu___108_16323.splice);
        is_native_tactic = (uu___108_16323.is_native_tactic);
        identifier_info = (uu___108_16323.identifier_info);
        tc_hooks = (uu___108_16323.tc_hooks);
        dsenv = (uu___108_16323.dsenv);
        dep_graph = (uu___108_16323.dep_graph)
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
    let uu____16351 = expected_typ env_  in
    ((let uu___109_16357 = env_  in
      {
        solver = (uu___109_16357.solver);
        range = (uu___109_16357.range);
        curmodule = (uu___109_16357.curmodule);
        gamma = (uu___109_16357.gamma);
        gamma_cache = (uu___109_16357.gamma_cache);
        modules = (uu___109_16357.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___109_16357.sigtab);
        is_pattern = (uu___109_16357.is_pattern);
        instantiate_imp = (uu___109_16357.instantiate_imp);
        effects = (uu___109_16357.effects);
        generalize = (uu___109_16357.generalize);
        letrecs = (uu___109_16357.letrecs);
        top_level = (uu___109_16357.top_level);
        check_uvars = (uu___109_16357.check_uvars);
        use_eq = false;
        is_iface = (uu___109_16357.is_iface);
        admit = (uu___109_16357.admit);
        lax = (uu___109_16357.lax);
        lax_universes = (uu___109_16357.lax_universes);
        failhard = (uu___109_16357.failhard);
        nosynth = (uu___109_16357.nosynth);
        tc_term = (uu___109_16357.tc_term);
        type_of = (uu___109_16357.type_of);
        universe_of = (uu___109_16357.universe_of);
        check_type_of = (uu___109_16357.check_type_of);
        use_bv_sorts = (uu___109_16357.use_bv_sorts);
        qtbl_name_and_index = (uu___109_16357.qtbl_name_and_index);
        normalized_eff_names = (uu___109_16357.normalized_eff_names);
        proof_ns = (uu___109_16357.proof_ns);
        synth_hook = (uu___109_16357.synth_hook);
        splice = (uu___109_16357.splice);
        is_native_tactic = (uu___109_16357.is_native_tactic);
        identifier_info = (uu___109_16357.identifier_info);
        tc_hooks = (uu___109_16357.tc_hooks);
        dsenv = (uu___109_16357.dsenv);
        dep_graph = (uu___109_16357.dep_graph)
      }), uu____16351)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid =
    let uu____16367 =
      let uu____16370 = FStar_Ident.id_of_text ""  in [uu____16370]  in
    FStar_Ident.lid_of_ids uu____16367  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____16376 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16376
        then
          let uu____16379 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___83_16389  ->
                    match uu___83_16389 with
                    | Binding_sig (uu____16392,se) -> [se]
                    | uu____16398 -> []))
             in
          FStar_All.pipe_right uu____16379 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___110_16405 = env  in
       {
         solver = (uu___110_16405.solver);
         range = (uu___110_16405.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___110_16405.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___110_16405.expected_typ);
         sigtab = (uu___110_16405.sigtab);
         is_pattern = (uu___110_16405.is_pattern);
         instantiate_imp = (uu___110_16405.instantiate_imp);
         effects = (uu___110_16405.effects);
         generalize = (uu___110_16405.generalize);
         letrecs = (uu___110_16405.letrecs);
         top_level = (uu___110_16405.top_level);
         check_uvars = (uu___110_16405.check_uvars);
         use_eq = (uu___110_16405.use_eq);
         is_iface = (uu___110_16405.is_iface);
         admit = (uu___110_16405.admit);
         lax = (uu___110_16405.lax);
         lax_universes = (uu___110_16405.lax_universes);
         failhard = (uu___110_16405.failhard);
         nosynth = (uu___110_16405.nosynth);
         tc_term = (uu___110_16405.tc_term);
         type_of = (uu___110_16405.type_of);
         universe_of = (uu___110_16405.universe_of);
         check_type_of = (uu___110_16405.check_type_of);
         use_bv_sorts = (uu___110_16405.use_bv_sorts);
         qtbl_name_and_index = (uu___110_16405.qtbl_name_and_index);
         normalized_eff_names = (uu___110_16405.normalized_eff_names);
         proof_ns = (uu___110_16405.proof_ns);
         synth_hook = (uu___110_16405.synth_hook);
         splice = (uu___110_16405.splice);
         is_native_tactic = (uu___110_16405.is_native_tactic);
         identifier_info = (uu___110_16405.identifier_info);
         tc_hooks = (uu___110_16405.tc_hooks);
         dsenv = (uu___110_16405.dsenv);
         dep_graph = (uu___110_16405.dep_graph)
       })
  
let uvars_in_env : env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____16496)::tl1 -> aux out tl1
      | (Binding_lid (uu____16500,(uu____16501,t)))::tl1 ->
          let uu____16516 =
            let uu____16523 = FStar_Syntax_Free.uvars t  in
            ext out uu____16523  in
          aux uu____16516 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16530;
            FStar_Syntax_Syntax.index = uu____16531;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16538 =
            let uu____16545 = FStar_Syntax_Free.uvars t  in
            ext out uu____16545  in
          aux uu____16538 tl1
      | (Binding_sig uu____16552)::uu____16553 -> out
      | (Binding_sig_inst uu____16562)::uu____16563 -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____16628)::tl1 -> aux out tl1
      | (Binding_univ uu____16640)::tl1 -> aux out tl1
      | (Binding_lid (uu____16644,(uu____16645,t)))::tl1 ->
          let uu____16660 =
            let uu____16663 = FStar_Syntax_Free.univs t  in
            ext out uu____16663  in
          aux uu____16660 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16666;
            FStar_Syntax_Syntax.index = uu____16667;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16674 =
            let uu____16677 = FStar_Syntax_Free.univs t  in
            ext out uu____16677  in
          aux uu____16674 tl1
      | (Binding_sig uu____16680)::uu____16681 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____16744)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____16760 = FStar_Util.set_add uname out  in
          aux uu____16760 tl1
      | (Binding_lid (uu____16763,(uu____16764,t)))::tl1 ->
          let uu____16779 =
            let uu____16782 = FStar_Syntax_Free.univnames t  in
            ext out uu____16782  in
          aux uu____16779 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16785;
            FStar_Syntax_Syntax.index = uu____16786;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16793 =
            let uu____16796 = FStar_Syntax_Free.univnames t  in
            ext out uu____16796  in
          aux uu____16793 tl1
      | (Binding_sig uu____16799)::uu____16800 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___84_16826  ->
            match uu___84_16826 with
            | Binding_var x -> [x]
            | Binding_lid uu____16830 -> []
            | Binding_sig uu____16835 -> []
            | Binding_univ uu____16842 -> []
            | Binding_sig_inst uu____16843 -> []))
  
let binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____16861 =
      let uu____16864 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____16864
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____16861 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> unit =
  fun env  ->
    let uu____16892 =
      let uu____16893 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___85_16903  ->
                match uu___85_16903 with
                | Binding_var x ->
                    let uu____16905 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____16905
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____16908) ->
                    let uu____16909 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____16909
                | Binding_sig (ls,uu____16911) ->
                    let uu____16916 =
                      let uu____16917 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____16917
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____16916
                | Binding_sig_inst (ls,uu____16927,uu____16928) ->
                    let uu____16933 =
                      let uu____16934 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____16934
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____16933))
         in
      FStar_All.pipe_right uu____16893 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____16892 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____16955 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____16955
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____16983  ->
                 fun uu____16984  ->
                   match (uu____16983, uu____16984) with
                   | ((b1,uu____17002),(b2,uu____17004)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let string_of_delta_level : delta_level -> Prims.string =
  fun uu___86_17055  ->
    match uu___86_17055 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____17056 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___87_17076  ->
             match uu___87_17076 with
             | Binding_sig (lids,uu____17082) -> FStar_List.append lids keys
             | uu____17087 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____17093  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let should_enc_path : env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____17135) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____17154,uu____17155) -> false  in
      let uu____17164 =
        FStar_List.tryFind
          (fun uu____17182  ->
             match uu____17182 with | (p,uu____17190) -> list_prefix p path)
          env.proof_ns
         in
      match uu____17164 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____17201,b) -> b
  
let should_enc_lid : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____17223 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____17223
  
let cons_proof_ns : Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___111_17241 = e  in
        {
          solver = (uu___111_17241.solver);
          range = (uu___111_17241.range);
          curmodule = (uu___111_17241.curmodule);
          gamma = (uu___111_17241.gamma);
          gamma_cache = (uu___111_17241.gamma_cache);
          modules = (uu___111_17241.modules);
          expected_typ = (uu___111_17241.expected_typ);
          sigtab = (uu___111_17241.sigtab);
          is_pattern = (uu___111_17241.is_pattern);
          instantiate_imp = (uu___111_17241.instantiate_imp);
          effects = (uu___111_17241.effects);
          generalize = (uu___111_17241.generalize);
          letrecs = (uu___111_17241.letrecs);
          top_level = (uu___111_17241.top_level);
          check_uvars = (uu___111_17241.check_uvars);
          use_eq = (uu___111_17241.use_eq);
          is_iface = (uu___111_17241.is_iface);
          admit = (uu___111_17241.admit);
          lax = (uu___111_17241.lax);
          lax_universes = (uu___111_17241.lax_universes);
          failhard = (uu___111_17241.failhard);
          nosynth = (uu___111_17241.nosynth);
          tc_term = (uu___111_17241.tc_term);
          type_of = (uu___111_17241.type_of);
          universe_of = (uu___111_17241.universe_of);
          check_type_of = (uu___111_17241.check_type_of);
          use_bv_sorts = (uu___111_17241.use_bv_sorts);
          qtbl_name_and_index = (uu___111_17241.qtbl_name_and_index);
          normalized_eff_names = (uu___111_17241.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___111_17241.synth_hook);
          splice = (uu___111_17241.splice);
          is_native_tactic = (uu___111_17241.is_native_tactic);
          identifier_info = (uu___111_17241.identifier_info);
          tc_hooks = (uu___111_17241.tc_hooks);
          dsenv = (uu___111_17241.dsenv);
          dep_graph = (uu___111_17241.dep_graph)
        }
  
let add_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path 
let rem_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path 
let get_proof_ns : env -> proof_namespace = fun e  -> e.proof_ns 
let set_proof_ns : proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___112_17281 = e  in
      {
        solver = (uu___112_17281.solver);
        range = (uu___112_17281.range);
        curmodule = (uu___112_17281.curmodule);
        gamma = (uu___112_17281.gamma);
        gamma_cache = (uu___112_17281.gamma_cache);
        modules = (uu___112_17281.modules);
        expected_typ = (uu___112_17281.expected_typ);
        sigtab = (uu___112_17281.sigtab);
        is_pattern = (uu___112_17281.is_pattern);
        instantiate_imp = (uu___112_17281.instantiate_imp);
        effects = (uu___112_17281.effects);
        generalize = (uu___112_17281.generalize);
        letrecs = (uu___112_17281.letrecs);
        top_level = (uu___112_17281.top_level);
        check_uvars = (uu___112_17281.check_uvars);
        use_eq = (uu___112_17281.use_eq);
        is_iface = (uu___112_17281.is_iface);
        admit = (uu___112_17281.admit);
        lax = (uu___112_17281.lax);
        lax_universes = (uu___112_17281.lax_universes);
        failhard = (uu___112_17281.failhard);
        nosynth = (uu___112_17281.nosynth);
        tc_term = (uu___112_17281.tc_term);
        type_of = (uu___112_17281.type_of);
        universe_of = (uu___112_17281.universe_of);
        check_type_of = (uu___112_17281.check_type_of);
        use_bv_sorts = (uu___112_17281.use_bv_sorts);
        qtbl_name_and_index = (uu___112_17281.qtbl_name_and_index);
        normalized_eff_names = (uu___112_17281.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___112_17281.synth_hook);
        splice = (uu___112_17281.splice);
        is_native_tactic = (uu___112_17281.is_native_tactic);
        identifier_info = (uu___112_17281.identifier_info);
        tc_hooks = (uu___112_17281.tc_hooks);
        dsenv = (uu___112_17281.dsenv);
        dep_graph = (uu___112_17281.dep_graph)
      }
  
let unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____17296 = FStar_Syntax_Free.names t  in
      let uu____17299 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____17296 uu____17299
  
let closed : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____17320 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____17320
  
let closed' : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____17328 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____17328
  
let string_of_proof_ns : env -> Prims.string =
  fun env  ->
    let aux uu____17347 =
      match uu____17347 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____17363 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____17363)
       in
    let uu____17365 =
      let uu____17368 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____17368 FStar_List.rev  in
    FStar_All.pipe_right uu____17365 (FStar_String.concat " ")
  
let dummy_solver : solver_t =
  {
    init = (fun uu____17385  -> ());
    push = (fun uu____17387  -> ());
    pop = (fun uu____17389  -> ());
    encode_modul = (fun uu____17392  -> fun uu____17393  -> ());
    encode_sig = (fun uu____17396  -> fun uu____17397  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____17403 =
             let uu____17410 = FStar_Options.peek ()  in (e, g, uu____17410)
              in
           [uu____17403]);
    solve = (fun uu____17426  -> fun uu____17427  -> fun uu____17428  -> ());
    finish = (fun uu____17434  -> ());
    refresh = (fun uu____17436  -> ())
  } 
let mk_copy : env -> env =
  fun en  ->
    let uu___113_17442 = en  in
    let uu____17443 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____17446 = FStar_Util.smap_copy en.sigtab  in
    let uu____17449 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___113_17442.solver);
      range = (uu___113_17442.range);
      curmodule = (uu___113_17442.curmodule);
      gamma = (uu___113_17442.gamma);
      gamma_cache = uu____17443;
      modules = (uu___113_17442.modules);
      expected_typ = (uu___113_17442.expected_typ);
      sigtab = uu____17446;
      is_pattern = (uu___113_17442.is_pattern);
      instantiate_imp = (uu___113_17442.instantiate_imp);
      effects = (uu___113_17442.effects);
      generalize = (uu___113_17442.generalize);
      letrecs = (uu___113_17442.letrecs);
      top_level = (uu___113_17442.top_level);
      check_uvars = (uu___113_17442.check_uvars);
      use_eq = (uu___113_17442.use_eq);
      is_iface = (uu___113_17442.is_iface);
      admit = (uu___113_17442.admit);
      lax = (uu___113_17442.lax);
      lax_universes = (uu___113_17442.lax_universes);
      failhard = (uu___113_17442.failhard);
      nosynth = (uu___113_17442.nosynth);
      tc_term = (uu___113_17442.tc_term);
      type_of = (uu___113_17442.type_of);
      universe_of = (uu___113_17442.universe_of);
      check_type_of = (uu___113_17442.check_type_of);
      use_bv_sorts = (uu___113_17442.use_bv_sorts);
      qtbl_name_and_index = (uu___113_17442.qtbl_name_and_index);
      normalized_eff_names = (uu___113_17442.normalized_eff_names);
      proof_ns = (uu___113_17442.proof_ns);
      synth_hook = (uu___113_17442.synth_hook);
      splice = (uu___113_17442.splice);
      is_native_tactic = (uu___113_17442.is_native_tactic);
      identifier_info = (uu___113_17442.identifier_info);
      tc_hooks = (uu___113_17442.tc_hooks);
      dsenv = uu____17449;
      dep_graph = (uu___113_17442.dep_graph)
    }
  