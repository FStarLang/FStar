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
                let uu____5975 = FStar_ToSyntax_Env.empty_env ()  in
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
  
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____6059 =
       let uu____6062 = FStar_ST.op_Bang stack  in env :: uu____6062  in
     FStar_ST.op_Colon_Equals stack uu____6059);
    (let uu___90_6111 = env  in
     let uu____6112 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6115 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6118 =
       let uu____6131 =
         let uu____6134 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____6134  in
       let uu____6159 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____6131, uu____6159)  in
     let uu____6200 =
       let uu____6203 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6203  in
     {
       solver = (uu___90_6111.solver);
       range = (uu___90_6111.range);
       curmodule = (uu___90_6111.curmodule);
       gamma = (uu___90_6111.gamma);
       gamma_cache = uu____6112;
       modules = (uu___90_6111.modules);
       expected_typ = (uu___90_6111.expected_typ);
       sigtab = uu____6115;
       is_pattern = (uu___90_6111.is_pattern);
       instantiate_imp = (uu___90_6111.instantiate_imp);
       effects = (uu___90_6111.effects);
       generalize = (uu___90_6111.generalize);
       letrecs = (uu___90_6111.letrecs);
       top_level = (uu___90_6111.top_level);
       check_uvars = (uu___90_6111.check_uvars);
       use_eq = (uu___90_6111.use_eq);
       is_iface = (uu___90_6111.is_iface);
       admit = (uu___90_6111.admit);
       lax = (uu___90_6111.lax);
       lax_universes = (uu___90_6111.lax_universes);
       failhard = (uu___90_6111.failhard);
       nosynth = (uu___90_6111.nosynth);
       tc_term = (uu___90_6111.tc_term);
       type_of = (uu___90_6111.type_of);
       universe_of = (uu___90_6111.universe_of);
       check_type_of = (uu___90_6111.check_type_of);
       use_bv_sorts = (uu___90_6111.use_bv_sorts);
       qtbl_name_and_index = uu____6118;
       proof_ns = (uu___90_6111.proof_ns);
       synth = (uu___90_6111.synth);
       is_native_tactic = (uu___90_6111.is_native_tactic);
       identifier_info = uu____6200;
       tc_hooks = (uu___90_6111.tc_hooks);
       dsenv = (uu___90_6111.dsenv);
       dep_graph = (uu___90_6111.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____6247  ->
    let uu____6248 = FStar_ST.op_Bang stack  in
    match uu____6248 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6302 -> failwith "Impossible: Too many pops"
  
let (push : env -> Prims.string -> env) =
  fun env  -> fun msg  -> (env.solver).push msg; push_stack env 
let (pop : env -> Prims.string -> env) =
  fun env  -> fun msg  -> (env.solver).pop msg; pop_stack () 
let (incr_query_index : env -> env) =
  fun env  ->
    match env.qtbl_name_and_index with
    | (uu____6322,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        (FStar_Util.smap_add tbl l.FStar_Ident.str
           (n1 + (Prims.parse_int "1"));
         (let uu___91_6355 = env  in
          {
            solver = (uu___91_6355.solver);
            range = (uu___91_6355.range);
            curmodule = (uu___91_6355.curmodule);
            gamma = (uu___91_6355.gamma);
            gamma_cache = (uu___91_6355.gamma_cache);
            modules = (uu___91_6355.modules);
            expected_typ = (uu___91_6355.expected_typ);
            sigtab = (uu___91_6355.sigtab);
            is_pattern = (uu___91_6355.is_pattern);
            instantiate_imp = (uu___91_6355.instantiate_imp);
            effects = (uu___91_6355.effects);
            generalize = (uu___91_6355.generalize);
            letrecs = (uu___91_6355.letrecs);
            top_level = (uu___91_6355.top_level);
            check_uvars = (uu___91_6355.check_uvars);
            use_eq = (uu___91_6355.use_eq);
            is_iface = (uu___91_6355.is_iface);
            admit = (uu___91_6355.admit);
            lax = (uu___91_6355.lax);
            lax_universes = (uu___91_6355.lax_universes);
            failhard = (uu___91_6355.failhard);
            nosynth = (uu___91_6355.nosynth);
            tc_term = (uu___91_6355.tc_term);
            type_of = (uu___91_6355.type_of);
            universe_of = (uu___91_6355.universe_of);
            check_type_of = (uu___91_6355.check_type_of);
            use_bv_sorts = (uu___91_6355.use_bv_sorts);
            qtbl_name_and_index =
              (tbl,
                (FStar_Pervasives_Native.Some
                   (l, (n1 + (Prims.parse_int "1")))));
            proof_ns = (uu___91_6355.proof_ns);
            synth = (uu___91_6355.synth);
            is_native_tactic = (uu___91_6355.is_native_tactic);
            identifier_info = (uu___91_6355.identifier_info);
            tc_hooks = (uu___91_6355.tc_hooks);
            dsenv = (uu___91_6355.dsenv);
            dep_graph = (uu___91_6355.dep_graph)
          }))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___92_6381 = e  in
         {
           solver = (uu___92_6381.solver);
           range = r;
           curmodule = (uu___92_6381.curmodule);
           gamma = (uu___92_6381.gamma);
           gamma_cache = (uu___92_6381.gamma_cache);
           modules = (uu___92_6381.modules);
           expected_typ = (uu___92_6381.expected_typ);
           sigtab = (uu___92_6381.sigtab);
           is_pattern = (uu___92_6381.is_pattern);
           instantiate_imp = (uu___92_6381.instantiate_imp);
           effects = (uu___92_6381.effects);
           generalize = (uu___92_6381.generalize);
           letrecs = (uu___92_6381.letrecs);
           top_level = (uu___92_6381.top_level);
           check_uvars = (uu___92_6381.check_uvars);
           use_eq = (uu___92_6381.use_eq);
           is_iface = (uu___92_6381.is_iface);
           admit = (uu___92_6381.admit);
           lax = (uu___92_6381.lax);
           lax_universes = (uu___92_6381.lax_universes);
           failhard = (uu___92_6381.failhard);
           nosynth = (uu___92_6381.nosynth);
           tc_term = (uu___92_6381.tc_term);
           type_of = (uu___92_6381.type_of);
           universe_of = (uu___92_6381.universe_of);
           check_type_of = (uu___92_6381.check_type_of);
           use_bv_sorts = (uu___92_6381.use_bv_sorts);
           qtbl_name_and_index = (uu___92_6381.qtbl_name_and_index);
           proof_ns = (uu___92_6381.proof_ns);
           synth = (uu___92_6381.synth);
           is_native_tactic = (uu___92_6381.is_native_tactic);
           identifier_info = (uu___92_6381.identifier_info);
           tc_hooks = (uu___92_6381.tc_hooks);
           dsenv = (uu___92_6381.dsenv);
           dep_graph = (uu___92_6381.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____6391 =
        let uu____6392 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____6392 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6391
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6440 =
          let uu____6441 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6441 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6440
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6489 =
          let uu____6490 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6490 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6489
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____6540 =
        let uu____6541 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____6541 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6540
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___93_6594 = env  in
      {
        solver = (uu___93_6594.solver);
        range = (uu___93_6594.range);
        curmodule = lid;
        gamma = (uu___93_6594.gamma);
        gamma_cache = (uu___93_6594.gamma_cache);
        modules = (uu___93_6594.modules);
        expected_typ = (uu___93_6594.expected_typ);
        sigtab = (uu___93_6594.sigtab);
        is_pattern = (uu___93_6594.is_pattern);
        instantiate_imp = (uu___93_6594.instantiate_imp);
        effects = (uu___93_6594.effects);
        generalize = (uu___93_6594.generalize);
        letrecs = (uu___93_6594.letrecs);
        top_level = (uu___93_6594.top_level);
        check_uvars = (uu___93_6594.check_uvars);
        use_eq = (uu___93_6594.use_eq);
        is_iface = (uu___93_6594.is_iface);
        admit = (uu___93_6594.admit);
        lax = (uu___93_6594.lax);
        lax_universes = (uu___93_6594.lax_universes);
        failhard = (uu___93_6594.failhard);
        nosynth = (uu___93_6594.nosynth);
        tc_term = (uu___93_6594.tc_term);
        type_of = (uu___93_6594.type_of);
        universe_of = (uu___93_6594.universe_of);
        check_type_of = (uu___93_6594.check_type_of);
        use_bv_sorts = (uu___93_6594.use_bv_sorts);
        qtbl_name_and_index = (uu___93_6594.qtbl_name_and_index);
        proof_ns = (uu___93_6594.proof_ns);
        synth = (uu___93_6594.synth);
        is_native_tactic = (uu___93_6594.is_native_tactic);
        identifier_info = (uu___93_6594.identifier_info);
        tc_hooks = (uu___93_6594.tc_hooks);
        dsenv = (uu___93_6594.dsenv);
        dep_graph = (uu___93_6594.dep_graph)
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
    let uu____6620 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____6620)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____6628 =
      let uu____6629 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____6629  in
    (FStar_Errors.Fatal_VariableNotFound, uu____6628)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____6632  ->
    let uu____6633 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____6633
  
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
      | ((formals,t),uu____6671) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____6695 = FStar_Syntax_Subst.subst vs t  in (us, uu____6695)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___72_6708  ->
    match uu___72_6708 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6732  -> new_u_univ ()))
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
      let uu____6745 = inst_tscheme t  in
      match uu____6745 with
      | (us,t1) ->
          let uu____6756 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____6756)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6768  ->
          match uu____6768 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6783 =
                         let uu____6784 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____6785 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____6786 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____6787 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6784 uu____6785 uu____6786 uu____6787
                          in
                       failwith uu____6783)
                    else ();
                    (let uu____6789 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____6789))
               | uu____6796 ->
                   let uu____6797 =
                     let uu____6798 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6798
                      in
                   failwith uu____6797)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____6802 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____6806 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6810 -> false
  
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
             | ([],uu____6844) -> Maybe
             | (uu____6851,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6870 -> No  in
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
          let uu____6955 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____6955 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___73_7000  ->
                   match uu___73_7000 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7043 =
                           let uu____7062 =
                             let uu____7077 = inst_tscheme t  in
                             FStar_Util.Inl uu____7077  in
                           (uu____7062, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7043
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7143,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7145);
                                     FStar_Syntax_Syntax.sigrng = uu____7146;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7147;
                                     FStar_Syntax_Syntax.sigmeta = uu____7148;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7149;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7169 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7169
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7215 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7222 -> cache t  in
                       let uu____7223 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7223 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7298 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7298 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7384 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7444 = find_in_sigtab env lid  in
         match uu____7444 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7523) ->
          add_sigelts env ses
      | uu____7532 ->
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
            | uu____7546 -> ()))

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
        (fun uu___74_7573  ->
           match uu___74_7573 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7591 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____7644,lb::[]),uu____7646) ->
            let uu____7659 =
              let uu____7668 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____7677 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____7668, uu____7677)  in
            FStar_Pervasives_Native.Some uu____7659
        | FStar_Syntax_Syntax.Sig_let ((uu____7690,lbs),uu____7692) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____7728 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____7740 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____7740
                     then
                       let uu____7751 =
                         let uu____7760 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____7769 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____7760, uu____7769)  in
                       FStar_Pervasives_Native.Some uu____7751
                     else FStar_Pervasives_Native.None)
        | uu____7791 -> FStar_Pervasives_Native.None
  
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
          let uu____7844 =
            let uu____7853 =
              let uu____7858 =
                let uu____7859 =
                  let uu____7862 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____7862
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____7859)  in
              inst_tscheme1 uu____7858  in
            (uu____7853, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____7844
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____7882,uu____7883) ->
          let uu____7888 =
            let uu____7897 =
              let uu____7902 =
                let uu____7903 =
                  let uu____7906 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____7906  in
                (us, uu____7903)  in
              inst_tscheme1 uu____7902  in
            (uu____7897, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____7888
      | uu____7923 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____8001 =
          match uu____8001 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____8097,uvs,t,uu____8100,uu____8101,uu____8102);
                      FStar_Syntax_Syntax.sigrng = uu____8103;
                      FStar_Syntax_Syntax.sigquals = uu____8104;
                      FStar_Syntax_Syntax.sigmeta = uu____8105;
                      FStar_Syntax_Syntax.sigattrs = uu____8106;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8127 =
                     let uu____8136 = inst_tscheme1 (uvs, t)  in
                     (uu____8136, rng)  in
                   FStar_Pervasives_Native.Some uu____8127
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____8156;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____8158;
                      FStar_Syntax_Syntax.sigattrs = uu____8159;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8176 =
                     let uu____8177 = in_cur_mod env l  in uu____8177 = Yes
                      in
                   if uu____8176
                   then
                     let uu____8188 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____8188
                      then
                        let uu____8201 =
                          let uu____8210 = inst_tscheme1 (uvs, t)  in
                          (uu____8210, rng)  in
                        FStar_Pervasives_Native.Some uu____8201
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____8237 =
                        let uu____8246 = inst_tscheme1 (uvs, t)  in
                        (uu____8246, rng)  in
                      FStar_Pervasives_Native.Some uu____8237)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8267,uu____8268);
                      FStar_Syntax_Syntax.sigrng = uu____8269;
                      FStar_Syntax_Syntax.sigquals = uu____8270;
                      FStar_Syntax_Syntax.sigmeta = uu____8271;
                      FStar_Syntax_Syntax.sigattrs = uu____8272;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____8311 =
                          let uu____8320 = inst_tscheme1 (uvs, k)  in
                          (uu____8320, rng)  in
                        FStar_Pervasives_Native.Some uu____8311
                    | uu____8337 ->
                        let uu____8338 =
                          let uu____8347 =
                            let uu____8352 =
                              let uu____8353 =
                                let uu____8356 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8356
                                 in
                              (uvs, uu____8353)  in
                            inst_tscheme1 uu____8352  in
                          (uu____8347, rng)  in
                        FStar_Pervasives_Native.Some uu____8338)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8377,uu____8378);
                      FStar_Syntax_Syntax.sigrng = uu____8379;
                      FStar_Syntax_Syntax.sigquals = uu____8380;
                      FStar_Syntax_Syntax.sigmeta = uu____8381;
                      FStar_Syntax_Syntax.sigattrs = uu____8382;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____8422 =
                          let uu____8431 = inst_tscheme_with (uvs, k) us  in
                          (uu____8431, rng)  in
                        FStar_Pervasives_Native.Some uu____8422
                    | uu____8448 ->
                        let uu____8449 =
                          let uu____8458 =
                            let uu____8463 =
                              let uu____8464 =
                                let uu____8467 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8467
                                 in
                              (uvs, uu____8464)  in
                            inst_tscheme_with uu____8463 us  in
                          (uu____8458, rng)  in
                        FStar_Pervasives_Native.Some uu____8449)
               | FStar_Util.Inr se ->
                   let uu____8501 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____8522;
                          FStar_Syntax_Syntax.sigrng = uu____8523;
                          FStar_Syntax_Syntax.sigquals = uu____8524;
                          FStar_Syntax_Syntax.sigmeta = uu____8525;
                          FStar_Syntax_Syntax.sigattrs = uu____8526;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____8541 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____8501
                     (FStar_Util.map_option
                        (fun uu____8589  ->
                           match uu____8589 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____8620 =
          let uu____8631 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____8631 mapper  in
        match uu____8620 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            FStar_Pervasives_Native.Some
              ((us,
                 (let uu___94_8724 = t  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___94_8724.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                    FStar_Syntax_Syntax.vars =
                      (uu___94_8724.FStar_Syntax_Syntax.vars)
                  })), r)
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____8749 = lookup_qname env l  in
      match uu____8749 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8768 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____8816 = try_lookup_bv env bv  in
      match uu____8816 with
      | FStar_Pervasives_Native.None  ->
          let uu____8831 = variable_not_found bv  in
          FStar_Errors.raise_error uu____8831 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8846 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____8847 =
            let uu____8848 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____8848  in
          (uu____8846, uu____8847)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____8865 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____8865 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____8931 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____8931  in
          let uu____8932 =
            let uu____8941 =
              let uu____8946 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____8946)  in
            (uu____8941, r1)  in
          FStar_Pervasives_Native.Some uu____8932
  
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
        let uu____8974 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____8974 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____9007,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____9032 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____9032  in
            let uu____9033 =
              let uu____9038 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____9038, r1)  in
            FStar_Pervasives_Native.Some uu____9033
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____9057 = try_lookup_lid env l  in
      match uu____9057 with
      | FStar_Pervasives_Native.None  ->
          let uu____9084 = name_not_found l  in
          FStar_Errors.raise_error uu____9084 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___75_9124  ->
              match uu___75_9124 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9126 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9141 = lookup_qname env lid  in
      match uu____9141 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9150,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9153;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9155;
              FStar_Syntax_Syntax.sigattrs = uu____9156;_},FStar_Pervasives_Native.None
            ),uu____9157)
          ->
          let uu____9206 =
            let uu____9217 =
              let uu____9222 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9222)  in
            (uu____9217, q)  in
          FStar_Pervasives_Native.Some uu____9206
      | uu____9239 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9256 = lookup_qname env lid  in
      match uu____9256 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9261,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9264;
              FStar_Syntax_Syntax.sigquals = uu____9265;
              FStar_Syntax_Syntax.sigmeta = uu____9266;
              FStar_Syntax_Syntax.sigattrs = uu____9267;_},FStar_Pervasives_Native.None
            ),uu____9268)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9317 ->
          let uu____9318 = name_not_found lid  in
          FStar_Errors.raise_error uu____9318 (FStar_Ident.range_of_lid lid)
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9337 = lookup_qname env lid  in
      match uu____9337 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9342,uvs,t,uu____9345,uu____9346,uu____9347);
              FStar_Syntax_Syntax.sigrng = uu____9348;
              FStar_Syntax_Syntax.sigquals = uu____9349;
              FStar_Syntax_Syntax.sigmeta = uu____9350;
              FStar_Syntax_Syntax.sigattrs = uu____9351;_},FStar_Pervasives_Native.None
            ),uu____9352)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9405 ->
          let uu____9406 = name_not_found lid  in
          FStar_Errors.raise_error uu____9406 (FStar_Ident.range_of_lid lid)
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9427 = lookup_qname env lid  in
      match uu____9427 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9434,uu____9435,uu____9436,uu____9437,uu____9438,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9440;
              FStar_Syntax_Syntax.sigquals = uu____9441;
              FStar_Syntax_Syntax.sigmeta = uu____9442;
              FStar_Syntax_Syntax.sigattrs = uu____9443;_},uu____9444),uu____9445)
          -> (true, dcs)
      | uu____9506 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____9515 = lookup_qname env lid  in
      match uu____9515 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9516,uu____9517,uu____9518,l,uu____9520,uu____9521);
              FStar_Syntax_Syntax.sigrng = uu____9522;
              FStar_Syntax_Syntax.sigquals = uu____9523;
              FStar_Syntax_Syntax.sigmeta = uu____9524;
              FStar_Syntax_Syntax.sigattrs = uu____9525;_},uu____9526),uu____9527)
          -> l
      | uu____9582 ->
          let uu____9583 =
            let uu____9584 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____9584  in
          failwith uu____9583
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9625) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9676,lbs),uu____9678) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____9706 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____9706
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9738 -> FStar_Pervasives_Native.None)
        | uu____9743 -> FStar_Pervasives_Native.None
  
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
        let uu____9767 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____9767
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____9790),uu____9791) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____9840 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9857 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____9857
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____9872 = lookup_qname env ftv  in
      match uu____9872 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9876) ->
          let uu____9921 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____9921 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9942,t),r) ->
               let uu____9957 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____9957)
      | uu____9958 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____9965 = try_lookup_effect_lid env ftv  in
      match uu____9965 with
      | FStar_Pervasives_Native.None  ->
          let uu____9968 = name_not_found ftv  in
          FStar_Errors.raise_error uu____9968 (FStar_Ident.range_of_lid ftv)
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
        let uu____9989 = lookup_qname env lid0  in
        match uu____9989 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10000);
                FStar_Syntax_Syntax.sigrng = uu____10001;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10003;
                FStar_Syntax_Syntax.sigattrs = uu____10004;_},FStar_Pervasives_Native.None
              ),uu____10005)
            ->
            let lid1 =
              let uu____10059 =
                let uu____10060 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10060
                 in
              FStar_Ident.set_lid_range lid uu____10059  in
            let uu____10061 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___76_10065  ->
                      match uu___76_10065 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10066 -> false))
               in
            if uu____10061
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10080 =
                      let uu____10081 =
                        let uu____10082 = get_range env  in
                        FStar_Range.string_of_range uu____10082  in
                      let uu____10083 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____10084 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10081 uu____10083 uu____10084
                       in
                    failwith uu____10080)
                  in
               match (binders, univs1) with
               | ([],uu____10091) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10108,uu____10109::uu____10110::uu____10111) ->
                   let uu____10116 =
                     let uu____10117 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____10118 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10117 uu____10118
                      in
                   failwith uu____10116
               | uu____10125 ->
                   let uu____10130 =
                     let uu____10135 =
                       let uu____10136 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____10136)  in
                     inst_tscheme_with uu____10135 insts  in
                   (match uu____10130 with
                    | (uu____10147,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____10150 =
                          let uu____10151 = FStar_Syntax_Subst.compress t1
                             in
                          uu____10151.FStar_Syntax_Syntax.n  in
                        (match uu____10150 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10198 -> failwith "Impossible")))
        | uu____10205 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10225 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____10225 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10238,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____10245 = find1 l2  in
            (match uu____10245 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____10252 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____10252 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10256 = find1 l  in
            (match uu____10256 with
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
      let uu____10270 = lookup_qname env l1  in
      match uu____10270 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10273;
              FStar_Syntax_Syntax.sigrng = uu____10274;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10276;
              FStar_Syntax_Syntax.sigattrs = uu____10277;_},uu____10278),uu____10279)
          -> q
      | uu____10330 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10343 =
          let uu____10344 =
            let uu____10345 = FStar_Util.string_of_int i  in
            let uu____10346 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10345 uu____10346
             in
          failwith uu____10344  in
        let uu____10347 = lookup_datacon env lid  in
        match uu____10347 with
        | (uu____10352,t) ->
            let uu____10354 =
              let uu____10355 = FStar_Syntax_Subst.compress t  in
              uu____10355.FStar_Syntax_Syntax.n  in
            (match uu____10354 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10359) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____10390 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____10390
                      FStar_Pervasives_Native.fst)
             | uu____10399 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____10406 = lookup_qname env l  in
      match uu____10406 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10407,uu____10408,uu____10409);
              FStar_Syntax_Syntax.sigrng = uu____10410;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10412;
              FStar_Syntax_Syntax.sigattrs = uu____10413;_},uu____10414),uu____10415)
          ->
          FStar_Util.for_some
            (fun uu___77_10468  ->
               match uu___77_10468 with
               | FStar_Syntax_Syntax.Projector uu____10469 -> true
               | uu____10474 -> false) quals
      | uu____10475 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____10482 = lookup_qname env lid  in
      match uu____10482 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10483,uu____10484,uu____10485,uu____10486,uu____10487,uu____10488);
              FStar_Syntax_Syntax.sigrng = uu____10489;
              FStar_Syntax_Syntax.sigquals = uu____10490;
              FStar_Syntax_Syntax.sigmeta = uu____10491;
              FStar_Syntax_Syntax.sigattrs = uu____10492;_},uu____10493),uu____10494)
          -> true
      | uu____10549 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____10556 = lookup_qname env lid  in
      match uu____10556 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10557,uu____10558,uu____10559,uu____10560,uu____10561,uu____10562);
              FStar_Syntax_Syntax.sigrng = uu____10563;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10565;
              FStar_Syntax_Syntax.sigattrs = uu____10566;_},uu____10567),uu____10568)
          ->
          FStar_Util.for_some
            (fun uu___78_10629  ->
               match uu___78_10629 with
               | FStar_Syntax_Syntax.RecordType uu____10630 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10639 -> true
               | uu____10648 -> false) quals
      | uu____10649 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____10653,uu____10654);
            FStar_Syntax_Syntax.sigrng = uu____10655;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____10657;
            FStar_Syntax_Syntax.sigattrs = uu____10658;_},uu____10659),uu____10660)
        ->
        FStar_Util.for_some
          (fun uu___79_10717  ->
             match uu___79_10717 with
             | FStar_Syntax_Syntax.Action uu____10718 -> true
             | uu____10719 -> false) quals
    | uu____10720 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____10727 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____10727
  
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
      let uu____10737 =
        let uu____10738 = FStar_Syntax_Util.un_uinst head1  in
        uu____10738.FStar_Syntax_Syntax.n  in
      match uu____10737 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10742 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____10749 = lookup_qname env l  in
      match uu____10749 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____10751),uu____10752) ->
          FStar_Util.for_some
            (fun uu___80_10800  ->
               match uu___80_10800 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____10801 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____10802 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10867 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10883) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10900 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10907 ->
                 FStar_Pervasives_Native.Some true
             | uu____10924 -> FStar_Pervasives_Native.Some false)
         in
      let uu____10925 =
        let uu____10928 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____10928 mapper  in
      match uu____10925 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____10974 = lookup_qname env lid  in
      match uu____10974 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10975,uu____10976,tps,uu____10978,uu____10979,uu____10980);
              FStar_Syntax_Syntax.sigrng = uu____10981;
              FStar_Syntax_Syntax.sigquals = uu____10982;
              FStar_Syntax_Syntax.sigmeta = uu____10983;
              FStar_Syntax_Syntax.sigattrs = uu____10984;_},uu____10985),uu____10986)
          -> FStar_List.length tps
      | uu____11049 ->
          let uu____11050 = name_not_found lid  in
          FStar_Errors.raise_error uu____11050 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____11094  ->
              match uu____11094 with
              | (d,uu____11102) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____11113 = effect_decl_opt env l  in
      match uu____11113 with
      | FStar_Pervasives_Native.None  ->
          let uu____11128 = name_not_found l  in
          FStar_Errors.raise_error uu____11128 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____11154  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11169  ->
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
            (let uu____11202 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11255  ->
                       match uu____11255 with
                       | (m1,m2,uu____11268,uu____11269,uu____11270) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____11202 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11287 =
                   let uu____11292 =
                     let uu____11293 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____11294 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11293
                       uu____11294
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____11292)
                    in
                 FStar_Errors.raise_error uu____11287 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11301,uu____11302,m3,j1,j2) -> (m3, j1, j2))
  
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
  'Auu____11339 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11339)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11366 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11392  ->
                match uu____11392 with
                | (d,uu____11398) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____11366 with
      | FStar_Pervasives_Native.None  ->
          let uu____11409 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____11409
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11422 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____11422 with
           | (uu____11433,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11443)::(wp,uu____11445)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11481 -> failwith "Impossible"))
  
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
                 let uu____11524 = get_range env  in
                 let uu____11525 =
                   let uu____11528 =
                     let uu____11529 =
                       let uu____11544 =
                         let uu____11547 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____11547]  in
                       (null_wp, uu____11544)  in
                     FStar_Syntax_Syntax.Tm_app uu____11529  in
                   FStar_Syntax_Syntax.mk uu____11528  in
                 uu____11525 FStar_Pervasives_Native.None uu____11524  in
               let uu____11553 =
                 let uu____11554 =
                   let uu____11563 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____11563]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11554;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____11553)
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___95_11572 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___95_11572.order);
              joins = (uu___95_11572.joins)
            }  in
          let uu___96_11581 = env  in
          {
            solver = (uu___96_11581.solver);
            range = (uu___96_11581.range);
            curmodule = (uu___96_11581.curmodule);
            gamma = (uu___96_11581.gamma);
            gamma_cache = (uu___96_11581.gamma_cache);
            modules = (uu___96_11581.modules);
            expected_typ = (uu___96_11581.expected_typ);
            sigtab = (uu___96_11581.sigtab);
            is_pattern = (uu___96_11581.is_pattern);
            instantiate_imp = (uu___96_11581.instantiate_imp);
            effects;
            generalize = (uu___96_11581.generalize);
            letrecs = (uu___96_11581.letrecs);
            top_level = (uu___96_11581.top_level);
            check_uvars = (uu___96_11581.check_uvars);
            use_eq = (uu___96_11581.use_eq);
            is_iface = (uu___96_11581.is_iface);
            admit = (uu___96_11581.admit);
            lax = (uu___96_11581.lax);
            lax_universes = (uu___96_11581.lax_universes);
            failhard = (uu___96_11581.failhard);
            nosynth = (uu___96_11581.nosynth);
            tc_term = (uu___96_11581.tc_term);
            type_of = (uu___96_11581.type_of);
            universe_of = (uu___96_11581.universe_of);
            check_type_of = (uu___96_11581.check_type_of);
            use_bv_sorts = (uu___96_11581.use_bv_sorts);
            qtbl_name_and_index = (uu___96_11581.qtbl_name_and_index);
            proof_ns = (uu___96_11581.proof_ns);
            synth = (uu___96_11581.synth);
            is_native_tactic = (uu___96_11581.is_native_tactic);
            identifier_info = (uu___96_11581.identifier_info);
            tc_hooks = (uu___96_11581.tc_hooks);
            dsenv = (uu___96_11581.dsenv);
            dep_graph = (uu___96_11581.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____11601 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____11601  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____11715 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____11716 = l1 u t wp e  in
                                l2 u t uu____11715 uu____11716))
                | uu____11717 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____11765 = inst_tscheme_with lift_t [u]  in
            match uu____11765 with
            | (uu____11772,lift_t1) ->
                let uu____11774 =
                  let uu____11777 =
                    let uu____11778 =
                      let uu____11793 =
                        let uu____11796 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____11797 =
                          let uu____11800 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____11800]  in
                        uu____11796 :: uu____11797  in
                      (lift_t1, uu____11793)  in
                    FStar_Syntax_Syntax.Tm_app uu____11778  in
                  FStar_Syntax_Syntax.mk uu____11777  in
                uu____11774 FStar_Pervasives_Native.None
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
            let uu____11850 = inst_tscheme_with lift_t [u]  in
            match uu____11850 with
            | (uu____11857,lift_t1) ->
                let uu____11859 =
                  let uu____11862 =
                    let uu____11863 =
                      let uu____11878 =
                        let uu____11881 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____11882 =
                          let uu____11885 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____11886 =
                            let uu____11889 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____11889]  in
                          uu____11885 :: uu____11886  in
                        uu____11881 :: uu____11882  in
                      (lift_t1, uu____11878)  in
                    FStar_Syntax_Syntax.Tm_app uu____11863  in
                  FStar_Syntax_Syntax.mk uu____11862  in
                uu____11859 FStar_Pervasives_Native.None
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
              let uu____11931 =
                let uu____11932 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____11932
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____11931  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____11936 =
              let uu____11937 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____11937  in
            let uu____11938 =
              let uu____11939 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11961 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____11961)
                 in
              FStar_Util.dflt "none" uu____11939  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11936
              uu____11938
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11987  ->
                    match uu____11987 with
                    | (e,uu____11995) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____12014 =
            match uu____12014 with
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
              let uu____12052 =
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
                                    (let uu____12073 =
                                       let uu____12082 =
                                         find_edge order1 (i, k)  in
                                       let uu____12085 =
                                         find_edge order1 (k, j)  in
                                       (uu____12082, uu____12085)  in
                                     match uu____12073 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12100 =
                                           compose_edges e1 e2  in
                                         [uu____12100]
                                     | uu____12101 -> [])))))
                 in
              FStar_List.append order1 uu____12052  in
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
                   let uu____12131 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12133 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____12133
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____12131
                   then
                     let uu____12138 =
                       let uu____12143 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12143)
                        in
                     let uu____12144 = get_range env  in
                     FStar_Errors.raise_error uu____12138 uu____12144
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
                                            let uu____12269 =
                                              let uu____12278 =
                                                find_edge order2 (i, k)  in
                                              let uu____12281 =
                                                find_edge order2 (j, k)  in
                                              (uu____12278, uu____12281)  in
                                            match uu____12269 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12323,uu____12324)
                                                     ->
                                                     let uu____12331 =
                                                       let uu____12336 =
                                                         let uu____12337 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12337
                                                          in
                                                       let uu____12340 =
                                                         let uu____12341 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12341
                                                          in
                                                       (uu____12336,
                                                         uu____12340)
                                                        in
                                                     (match uu____12331 with
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
                                            | uu____12376 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___97_12449 = env.effects  in
              { decls = (uu___97_12449.decls); order = order2; joins }  in
            let uu___98_12450 = env  in
            {
              solver = (uu___98_12450.solver);
              range = (uu___98_12450.range);
              curmodule = (uu___98_12450.curmodule);
              gamma = (uu___98_12450.gamma);
              gamma_cache = (uu___98_12450.gamma_cache);
              modules = (uu___98_12450.modules);
              expected_typ = (uu___98_12450.expected_typ);
              sigtab = (uu___98_12450.sigtab);
              is_pattern = (uu___98_12450.is_pattern);
              instantiate_imp = (uu___98_12450.instantiate_imp);
              effects;
              generalize = (uu___98_12450.generalize);
              letrecs = (uu___98_12450.letrecs);
              top_level = (uu___98_12450.top_level);
              check_uvars = (uu___98_12450.check_uvars);
              use_eq = (uu___98_12450.use_eq);
              is_iface = (uu___98_12450.is_iface);
              admit = (uu___98_12450.admit);
              lax = (uu___98_12450.lax);
              lax_universes = (uu___98_12450.lax_universes);
              failhard = (uu___98_12450.failhard);
              nosynth = (uu___98_12450.nosynth);
              tc_term = (uu___98_12450.tc_term);
              type_of = (uu___98_12450.type_of);
              universe_of = (uu___98_12450.universe_of);
              check_type_of = (uu___98_12450.check_type_of);
              use_bv_sorts = (uu___98_12450.use_bv_sorts);
              qtbl_name_and_index = (uu___98_12450.qtbl_name_and_index);
              proof_ns = (uu___98_12450.proof_ns);
              synth = (uu___98_12450.synth);
              is_native_tactic = (uu___98_12450.is_native_tactic);
              identifier_info = (uu___98_12450.identifier_info);
              tc_hooks = (uu___98_12450.tc_hooks);
              dsenv = (uu___98_12450.dsenv);
              dep_graph = (uu___98_12450.dep_graph)
            }))
      | uu____12451 -> env
  
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
        | uu____12475 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____12483 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____12483 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12500 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____12500 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12518 =
                     let uu____12523 =
                       let uu____12524 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____12529 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____12536 =
                         let uu____12537 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____12537  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____12524 uu____12529 uu____12536
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____12523)
                      in
                   FStar_Errors.raise_error uu____12518
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____12542 =
                     let uu____12551 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____12551 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____12568  ->
                        fun uu____12569  ->
                          match (uu____12568, uu____12569) with
                          | ((x,uu____12591),(t,uu____12593)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12542
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____12612 =
                     let uu___99_12613 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___99_12613.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___99_12613.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___99_12613.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___99_12613.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____12612
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
          let uu____12635 = effect_decl_opt env effect_name  in
          match uu____12635 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12668 =
                only_reifiable &&
                  (let uu____12670 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____12670)
                 in
              if uu____12668
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12686 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____12705 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____12734 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____12734
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____12735 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____12735
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____12745 =
                       let uu____12748 = get_range env  in
                       let uu____12749 =
                         let uu____12752 =
                           let uu____12753 =
                             let uu____12768 =
                               let uu____12771 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____12771; wp]  in
                             (repr, uu____12768)  in
                           FStar_Syntax_Syntax.Tm_app uu____12753  in
                         FStar_Syntax_Syntax.mk uu____12752  in
                       uu____12749 FStar_Pervasives_Native.None uu____12748
                        in
                     FStar_Pervasives_Native.Some uu____12745)
  
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
          let uu____12817 =
            let uu____12822 =
              let uu____12823 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____12823
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____12822)  in
          let uu____12824 = get_range env  in
          FStar_Errors.raise_error uu____12817 uu____12824  in
        let uu____12825 = effect_repr_aux true env c u_c  in
        match uu____12825 with
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
      | uu____12859 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____12866 =
        let uu____12867 = FStar_Syntax_Subst.compress t  in
        uu____12867.FStar_Syntax_Syntax.n  in
      match uu____12866 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12870,c) ->
          is_reifiable_comp env c
      | uu____12888 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12910)::uu____12911 -> x :: rest
        | (Binding_sig_inst uu____12920)::uu____12921 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12936 = push1 x rest1  in local :: uu____12936
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___100_12940 = env  in
       let uu____12941 = push1 s env.gamma  in
       {
         solver = (uu___100_12940.solver);
         range = (uu___100_12940.range);
         curmodule = (uu___100_12940.curmodule);
         gamma = uu____12941;
         gamma_cache = (uu___100_12940.gamma_cache);
         modules = (uu___100_12940.modules);
         expected_typ = (uu___100_12940.expected_typ);
         sigtab = (uu___100_12940.sigtab);
         is_pattern = (uu___100_12940.is_pattern);
         instantiate_imp = (uu___100_12940.instantiate_imp);
         effects = (uu___100_12940.effects);
         generalize = (uu___100_12940.generalize);
         letrecs = (uu___100_12940.letrecs);
         top_level = (uu___100_12940.top_level);
         check_uvars = (uu___100_12940.check_uvars);
         use_eq = (uu___100_12940.use_eq);
         is_iface = (uu___100_12940.is_iface);
         admit = (uu___100_12940.admit);
         lax = (uu___100_12940.lax);
         lax_universes = (uu___100_12940.lax_universes);
         failhard = (uu___100_12940.failhard);
         nosynth = (uu___100_12940.nosynth);
         tc_term = (uu___100_12940.tc_term);
         type_of = (uu___100_12940.type_of);
         universe_of = (uu___100_12940.universe_of);
         check_type_of = (uu___100_12940.check_type_of);
         use_bv_sorts = (uu___100_12940.use_bv_sorts);
         qtbl_name_and_index = (uu___100_12940.qtbl_name_and_index);
         proof_ns = (uu___100_12940.proof_ns);
         synth = (uu___100_12940.synth);
         is_native_tactic = (uu___100_12940.is_native_tactic);
         identifier_info = (uu___100_12940.identifier_info);
         tc_hooks = (uu___100_12940.tc_hooks);
         dsenv = (uu___100_12940.dsenv);
         dep_graph = (uu___100_12940.dep_graph)
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
      let uu___101_12971 = env  in
      {
        solver = (uu___101_12971.solver);
        range = (uu___101_12971.range);
        curmodule = (uu___101_12971.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___101_12971.gamma_cache);
        modules = (uu___101_12971.modules);
        expected_typ = (uu___101_12971.expected_typ);
        sigtab = (uu___101_12971.sigtab);
        is_pattern = (uu___101_12971.is_pattern);
        instantiate_imp = (uu___101_12971.instantiate_imp);
        effects = (uu___101_12971.effects);
        generalize = (uu___101_12971.generalize);
        letrecs = (uu___101_12971.letrecs);
        top_level = (uu___101_12971.top_level);
        check_uvars = (uu___101_12971.check_uvars);
        use_eq = (uu___101_12971.use_eq);
        is_iface = (uu___101_12971.is_iface);
        admit = (uu___101_12971.admit);
        lax = (uu___101_12971.lax);
        lax_universes = (uu___101_12971.lax_universes);
        failhard = (uu___101_12971.failhard);
        nosynth = (uu___101_12971.nosynth);
        tc_term = (uu___101_12971.tc_term);
        type_of = (uu___101_12971.type_of);
        universe_of = (uu___101_12971.universe_of);
        check_type_of = (uu___101_12971.check_type_of);
        use_bv_sorts = (uu___101_12971.use_bv_sorts);
        qtbl_name_and_index = (uu___101_12971.qtbl_name_and_index);
        proof_ns = (uu___101_12971.proof_ns);
        synth = (uu___101_12971.synth);
        is_native_tactic = (uu___101_12971.is_native_tactic);
        identifier_info = (uu___101_12971.identifier_info);
        tc_hooks = (uu___101_12971.tc_hooks);
        dsenv = (uu___101_12971.dsenv);
        dep_graph = (uu___101_12971.dep_graph)
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
            (let uu___102_13002 = env  in
             {
               solver = (uu___102_13002.solver);
               range = (uu___102_13002.range);
               curmodule = (uu___102_13002.curmodule);
               gamma = rest;
               gamma_cache = (uu___102_13002.gamma_cache);
               modules = (uu___102_13002.modules);
               expected_typ = (uu___102_13002.expected_typ);
               sigtab = (uu___102_13002.sigtab);
               is_pattern = (uu___102_13002.is_pattern);
               instantiate_imp = (uu___102_13002.instantiate_imp);
               effects = (uu___102_13002.effects);
               generalize = (uu___102_13002.generalize);
               letrecs = (uu___102_13002.letrecs);
               top_level = (uu___102_13002.top_level);
               check_uvars = (uu___102_13002.check_uvars);
               use_eq = (uu___102_13002.use_eq);
               is_iface = (uu___102_13002.is_iface);
               admit = (uu___102_13002.admit);
               lax = (uu___102_13002.lax);
               lax_universes = (uu___102_13002.lax_universes);
               failhard = (uu___102_13002.failhard);
               nosynth = (uu___102_13002.nosynth);
               tc_term = (uu___102_13002.tc_term);
               type_of = (uu___102_13002.type_of);
               universe_of = (uu___102_13002.universe_of);
               check_type_of = (uu___102_13002.check_type_of);
               use_bv_sorts = (uu___102_13002.use_bv_sorts);
               qtbl_name_and_index = (uu___102_13002.qtbl_name_and_index);
               proof_ns = (uu___102_13002.proof_ns);
               synth = (uu___102_13002.synth);
               is_native_tactic = (uu___102_13002.is_native_tactic);
               identifier_info = (uu___102_13002.identifier_info);
               tc_hooks = (uu___102_13002.tc_hooks);
               dsenv = (uu___102_13002.dsenv);
               dep_graph = (uu___102_13002.dep_graph)
             }))
    | uu____13003 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13025  ->
             match uu____13025 with | (x,uu____13031) -> push_bv env1 x) env
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
            let uu___103_13059 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___103_13059.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___103_13059.FStar_Syntax_Syntax.index);
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
      (let uu___104_13089 = env  in
       {
         solver = (uu___104_13089.solver);
         range = (uu___104_13089.range);
         curmodule = (uu___104_13089.curmodule);
         gamma = [];
         gamma_cache = (uu___104_13089.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___104_13089.sigtab);
         is_pattern = (uu___104_13089.is_pattern);
         instantiate_imp = (uu___104_13089.instantiate_imp);
         effects = (uu___104_13089.effects);
         generalize = (uu___104_13089.generalize);
         letrecs = (uu___104_13089.letrecs);
         top_level = (uu___104_13089.top_level);
         check_uvars = (uu___104_13089.check_uvars);
         use_eq = (uu___104_13089.use_eq);
         is_iface = (uu___104_13089.is_iface);
         admit = (uu___104_13089.admit);
         lax = (uu___104_13089.lax);
         lax_universes = (uu___104_13089.lax_universes);
         failhard = (uu___104_13089.failhard);
         nosynth = (uu___104_13089.nosynth);
         tc_term = (uu___104_13089.tc_term);
         type_of = (uu___104_13089.type_of);
         universe_of = (uu___104_13089.universe_of);
         check_type_of = (uu___104_13089.check_type_of);
         use_bv_sorts = (uu___104_13089.use_bv_sorts);
         qtbl_name_and_index = (uu___104_13089.qtbl_name_and_index);
         proof_ns = (uu___104_13089.proof_ns);
         synth = (uu___104_13089.synth);
         is_native_tactic = (uu___104_13089.is_native_tactic);
         identifier_info = (uu___104_13089.identifier_info);
         tc_hooks = (uu___104_13089.tc_hooks);
         dsenv = (uu___104_13089.dsenv);
         dep_graph = (uu___104_13089.dep_graph)
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
        let uu____13121 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____13121 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____13149 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____13149)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___105_13162 = env  in
      {
        solver = (uu___105_13162.solver);
        range = (uu___105_13162.range);
        curmodule = (uu___105_13162.curmodule);
        gamma = (uu___105_13162.gamma);
        gamma_cache = (uu___105_13162.gamma_cache);
        modules = (uu___105_13162.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___105_13162.sigtab);
        is_pattern = (uu___105_13162.is_pattern);
        instantiate_imp = (uu___105_13162.instantiate_imp);
        effects = (uu___105_13162.effects);
        generalize = (uu___105_13162.generalize);
        letrecs = (uu___105_13162.letrecs);
        top_level = (uu___105_13162.top_level);
        check_uvars = (uu___105_13162.check_uvars);
        use_eq = false;
        is_iface = (uu___105_13162.is_iface);
        admit = (uu___105_13162.admit);
        lax = (uu___105_13162.lax);
        lax_universes = (uu___105_13162.lax_universes);
        failhard = (uu___105_13162.failhard);
        nosynth = (uu___105_13162.nosynth);
        tc_term = (uu___105_13162.tc_term);
        type_of = (uu___105_13162.type_of);
        universe_of = (uu___105_13162.universe_of);
        check_type_of = (uu___105_13162.check_type_of);
        use_bv_sorts = (uu___105_13162.use_bv_sorts);
        qtbl_name_and_index = (uu___105_13162.qtbl_name_and_index);
        proof_ns = (uu___105_13162.proof_ns);
        synth = (uu___105_13162.synth);
        is_native_tactic = (uu___105_13162.is_native_tactic);
        identifier_info = (uu___105_13162.identifier_info);
        tc_hooks = (uu___105_13162.tc_hooks);
        dsenv = (uu___105_13162.dsenv);
        dep_graph = (uu___105_13162.dep_graph)
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
    let uu____13186 = expected_typ env_  in
    ((let uu___106_13192 = env_  in
      {
        solver = (uu___106_13192.solver);
        range = (uu___106_13192.range);
        curmodule = (uu___106_13192.curmodule);
        gamma = (uu___106_13192.gamma);
        gamma_cache = (uu___106_13192.gamma_cache);
        modules = (uu___106_13192.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___106_13192.sigtab);
        is_pattern = (uu___106_13192.is_pattern);
        instantiate_imp = (uu___106_13192.instantiate_imp);
        effects = (uu___106_13192.effects);
        generalize = (uu___106_13192.generalize);
        letrecs = (uu___106_13192.letrecs);
        top_level = (uu___106_13192.top_level);
        check_uvars = (uu___106_13192.check_uvars);
        use_eq = false;
        is_iface = (uu___106_13192.is_iface);
        admit = (uu___106_13192.admit);
        lax = (uu___106_13192.lax);
        lax_universes = (uu___106_13192.lax_universes);
        failhard = (uu___106_13192.failhard);
        nosynth = (uu___106_13192.nosynth);
        tc_term = (uu___106_13192.tc_term);
        type_of = (uu___106_13192.type_of);
        universe_of = (uu___106_13192.universe_of);
        check_type_of = (uu___106_13192.check_type_of);
        use_bv_sorts = (uu___106_13192.use_bv_sorts);
        qtbl_name_and_index = (uu___106_13192.qtbl_name_and_index);
        proof_ns = (uu___106_13192.proof_ns);
        synth = (uu___106_13192.synth);
        is_native_tactic = (uu___106_13192.is_native_tactic);
        identifier_info = (uu___106_13192.identifier_info);
        tc_hooks = (uu___106_13192.tc_hooks);
        dsenv = (uu___106_13192.dsenv);
        dep_graph = (uu___106_13192.dep_graph)
      }), uu____13186)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13205 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___81_13215  ->
                    match uu___81_13215 with
                    | Binding_sig (uu____13218,se) -> [se]
                    | uu____13224 -> []))
             in
          FStar_All.pipe_right uu____13205 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___107_13231 = env  in
       {
         solver = (uu___107_13231.solver);
         range = (uu___107_13231.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___107_13231.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___107_13231.expected_typ);
         sigtab = (uu___107_13231.sigtab);
         is_pattern = (uu___107_13231.is_pattern);
         instantiate_imp = (uu___107_13231.instantiate_imp);
         effects = (uu___107_13231.effects);
         generalize = (uu___107_13231.generalize);
         letrecs = (uu___107_13231.letrecs);
         top_level = (uu___107_13231.top_level);
         check_uvars = (uu___107_13231.check_uvars);
         use_eq = (uu___107_13231.use_eq);
         is_iface = (uu___107_13231.is_iface);
         admit = (uu___107_13231.admit);
         lax = (uu___107_13231.lax);
         lax_universes = (uu___107_13231.lax_universes);
         failhard = (uu___107_13231.failhard);
         nosynth = (uu___107_13231.nosynth);
         tc_term = (uu___107_13231.tc_term);
         type_of = (uu___107_13231.type_of);
         universe_of = (uu___107_13231.universe_of);
         check_type_of = (uu___107_13231.check_type_of);
         use_bv_sorts = (uu___107_13231.use_bv_sorts);
         qtbl_name_and_index = (uu___107_13231.qtbl_name_and_index);
         proof_ns = (uu___107_13231.proof_ns);
         synth = (uu___107_13231.synth);
         is_native_tactic = (uu___107_13231.is_native_tactic);
         identifier_info = (uu___107_13231.identifier_info);
         tc_hooks = (uu___107_13231.tc_hooks);
         dsenv = (uu___107_13231.dsenv);
         dep_graph = (uu___107_13231.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13312)::tl1 -> aux out tl1
      | (Binding_lid (uu____13316,(uu____13317,t)))::tl1 ->
          let uu____13332 =
            let uu____13339 = FStar_Syntax_Free.uvars t  in
            ext out uu____13339  in
          aux uu____13332 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13346;
            FStar_Syntax_Syntax.index = uu____13347;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13354 =
            let uu____13361 = FStar_Syntax_Free.uvars t  in
            ext out uu____13361  in
          aux uu____13354 tl1
      | (Binding_sig uu____13368)::uu____13369 -> out
      | (Binding_sig_inst uu____13378)::uu____13379 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13434)::tl1 -> aux out tl1
      | (Binding_univ uu____13446)::tl1 -> aux out tl1
      | (Binding_lid (uu____13450,(uu____13451,t)))::tl1 ->
          let uu____13466 =
            let uu____13469 = FStar_Syntax_Free.univs t  in
            ext out uu____13469  in
          aux uu____13466 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13472;
            FStar_Syntax_Syntax.index = uu____13473;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13480 =
            let uu____13483 = FStar_Syntax_Free.univs t  in
            ext out uu____13483  in
          aux uu____13480 tl1
      | (Binding_sig uu____13486)::uu____13487 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13540)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13556 = FStar_Util.fifo_set_add uname out  in
          aux uu____13556 tl1
      | (Binding_lid (uu____13559,(uu____13560,t)))::tl1 ->
          let uu____13575 =
            let uu____13578 = FStar_Syntax_Free.univnames t  in
            ext out uu____13578  in
          aux uu____13575 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13581;
            FStar_Syntax_Syntax.index = uu____13582;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13589 =
            let uu____13592 = FStar_Syntax_Free.univnames t  in
            ext out uu____13592  in
          aux uu____13589 tl1
      | (Binding_sig uu____13595)::uu____13596 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___82_13620  ->
            match uu___82_13620 with
            | Binding_var x -> [x]
            | Binding_lid uu____13624 -> []
            | Binding_sig uu____13629 -> []
            | Binding_univ uu____13636 -> []
            | Binding_sig_inst uu____13637 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____13653 =
      let uu____13656 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____13656
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____13653 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____13678 =
      let uu____13679 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___83_13689  ->
                match uu___83_13689 with
                | Binding_var x ->
                    let uu____13691 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____13691
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13694) ->
                    let uu____13695 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____13695
                | Binding_sig (ls,uu____13697) ->
                    let uu____13702 =
                      let uu____13703 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____13703
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____13702
                | Binding_sig_inst (ls,uu____13713,uu____13714) ->
                    let uu____13719 =
                      let uu____13720 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____13720
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____13719))
         in
      FStar_All.pipe_right uu____13679 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____13678 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____13737 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____13737
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13765  ->
                 fun uu____13766  ->
                   match (uu____13765, uu____13766) with
                   | ((b1,uu____13784),(b2,uu____13786)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___84_13828  ->
    match uu___84_13828 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____13829 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___85_13847  ->
             match uu___85_13847 with
             | Binding_sig (lids,uu____13853) -> FStar_List.append lids keys
             | uu____13858 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13864  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13898) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13917,uu____13918) -> false  in
      let uu____13927 =
        FStar_List.tryFind
          (fun uu____13945  ->
             match uu____13945 with | (p,uu____13953) -> list_prefix p path)
          env.proof_ns
         in
      match uu____13927 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____13964,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13982 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____13982
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___108_13994 = e  in
        {
          solver = (uu___108_13994.solver);
          range = (uu___108_13994.range);
          curmodule = (uu___108_13994.curmodule);
          gamma = (uu___108_13994.gamma);
          gamma_cache = (uu___108_13994.gamma_cache);
          modules = (uu___108_13994.modules);
          expected_typ = (uu___108_13994.expected_typ);
          sigtab = (uu___108_13994.sigtab);
          is_pattern = (uu___108_13994.is_pattern);
          instantiate_imp = (uu___108_13994.instantiate_imp);
          effects = (uu___108_13994.effects);
          generalize = (uu___108_13994.generalize);
          letrecs = (uu___108_13994.letrecs);
          top_level = (uu___108_13994.top_level);
          check_uvars = (uu___108_13994.check_uvars);
          use_eq = (uu___108_13994.use_eq);
          is_iface = (uu___108_13994.is_iface);
          admit = (uu___108_13994.admit);
          lax = (uu___108_13994.lax);
          lax_universes = (uu___108_13994.lax_universes);
          failhard = (uu___108_13994.failhard);
          nosynth = (uu___108_13994.nosynth);
          tc_term = (uu___108_13994.tc_term);
          type_of = (uu___108_13994.type_of);
          universe_of = (uu___108_13994.universe_of);
          check_type_of = (uu___108_13994.check_type_of);
          use_bv_sorts = (uu___108_13994.use_bv_sorts);
          qtbl_name_and_index = (uu___108_13994.qtbl_name_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___108_13994.synth);
          is_native_tactic = (uu___108_13994.is_native_tactic);
          identifier_info = (uu___108_13994.identifier_info);
          tc_hooks = (uu___108_13994.tc_hooks);
          dsenv = (uu___108_13994.dsenv);
          dep_graph = (uu___108_13994.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___109_14020 = e  in
      {
        solver = (uu___109_14020.solver);
        range = (uu___109_14020.range);
        curmodule = (uu___109_14020.curmodule);
        gamma = (uu___109_14020.gamma);
        gamma_cache = (uu___109_14020.gamma_cache);
        modules = (uu___109_14020.modules);
        expected_typ = (uu___109_14020.expected_typ);
        sigtab = (uu___109_14020.sigtab);
        is_pattern = (uu___109_14020.is_pattern);
        instantiate_imp = (uu___109_14020.instantiate_imp);
        effects = (uu___109_14020.effects);
        generalize = (uu___109_14020.generalize);
        letrecs = (uu___109_14020.letrecs);
        top_level = (uu___109_14020.top_level);
        check_uvars = (uu___109_14020.check_uvars);
        use_eq = (uu___109_14020.use_eq);
        is_iface = (uu___109_14020.is_iface);
        admit = (uu___109_14020.admit);
        lax = (uu___109_14020.lax);
        lax_universes = (uu___109_14020.lax_universes);
        failhard = (uu___109_14020.failhard);
        nosynth = (uu___109_14020.nosynth);
        tc_term = (uu___109_14020.tc_term);
        type_of = (uu___109_14020.type_of);
        universe_of = (uu___109_14020.universe_of);
        check_type_of = (uu___109_14020.check_type_of);
        use_bv_sorts = (uu___109_14020.use_bv_sorts);
        qtbl_name_and_index = (uu___109_14020.qtbl_name_and_index);
        proof_ns = ns;
        synth = (uu___109_14020.synth);
        is_native_tactic = (uu___109_14020.is_native_tactic);
        identifier_info = (uu___109_14020.identifier_info);
        tc_hooks = (uu___109_14020.tc_hooks);
        dsenv = (uu___109_14020.dsenv);
        dep_graph = (uu___109_14020.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____14031 = FStar_Syntax_Free.names t  in
      let uu____14034 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14031 uu____14034
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____14051 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____14051
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14057 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____14057
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____14072 =
      match uu____14072 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14088 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____14088)
       in
    let uu____14090 =
      let uu____14093 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____14093 FStar_List.rev  in
    FStar_All.pipe_right uu____14090 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____14110  -> ());
    push = (fun uu____14112  -> ());
    pop = (fun uu____14114  -> ());
    encode_modul = (fun uu____14117  -> fun uu____14118  -> ());
    encode_sig = (fun uu____14121  -> fun uu____14122  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14128 =
             let uu____14135 = FStar_Options.peek ()  in (e, g, uu____14135)
              in
           [uu____14128]);
    solve = (fun uu____14151  -> fun uu____14152  -> fun uu____14153  -> ());
    finish = (fun uu____14159  -> ());
    refresh = (fun uu____14161  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___110_14165 = en  in
    let uu____14166 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____14169 = FStar_Util.smap_copy en.sigtab  in
    let uu____14172 = FStar_ToSyntax_Env.mk_copy en.dsenv  in
    {
      solver = (uu___110_14165.solver);
      range = (uu___110_14165.range);
      curmodule = (uu___110_14165.curmodule);
      gamma = (uu___110_14165.gamma);
      gamma_cache = uu____14166;
      modules = (uu___110_14165.modules);
      expected_typ = (uu___110_14165.expected_typ);
      sigtab = uu____14169;
      is_pattern = (uu___110_14165.is_pattern);
      instantiate_imp = (uu___110_14165.instantiate_imp);
      effects = (uu___110_14165.effects);
      generalize = (uu___110_14165.generalize);
      letrecs = (uu___110_14165.letrecs);
      top_level = (uu___110_14165.top_level);
      check_uvars = (uu___110_14165.check_uvars);
      use_eq = (uu___110_14165.use_eq);
      is_iface = (uu___110_14165.is_iface);
      admit = (uu___110_14165.admit);
      lax = (uu___110_14165.lax);
      lax_universes = (uu___110_14165.lax_universes);
      failhard = (uu___110_14165.failhard);
      nosynth = (uu___110_14165.nosynth);
      tc_term = (uu___110_14165.tc_term);
      type_of = (uu___110_14165.type_of);
      universe_of = (uu___110_14165.universe_of);
      check_type_of = (uu___110_14165.check_type_of);
      use_bv_sorts = (uu___110_14165.use_bv_sorts);
      qtbl_name_and_index = (uu___110_14165.qtbl_name_and_index);
      proof_ns = (uu___110_14165.proof_ns);
      synth = (uu___110_14165.synth);
      is_native_tactic = (uu___110_14165.is_native_tactic);
      identifier_info = (uu___110_14165.identifier_info);
      tc_hooks = (uu___110_14165.tc_hooks);
      dsenv = uu____14172;
      dep_graph = (uu___110_14165.dep_graph)
    }
  