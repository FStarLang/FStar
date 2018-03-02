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
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6085  ->
    let uu____6086 = FStar_ST.op_Bang query_indices  in
    match uu____6086 with
    | [] -> failwith "Empty query indices!"
    | uu____6136 ->
        let uu____6145 =
          let uu____6154 =
            let uu____6161 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____6161  in
          let uu____6211 = FStar_ST.op_Bang query_indices  in uu____6154 ::
            uu____6211
           in
        FStar_ST.op_Colon_Equals query_indices uu____6145
  
let (pop_query_indices : Prims.unit -> Prims.unit) =
  fun uu____6298  ->
    let uu____6299 = FStar_ST.op_Bang query_indices  in
    match uu____6299 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____6412  ->
    match uu____6412 with
    | (l,n1) ->
        let uu____6419 = FStar_ST.op_Bang query_indices  in
        (match uu____6419 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6530 -> failwith "Empty query indices")
  
let (peek_query_indices :
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6547  ->
    let uu____6548 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____6548
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____6619 =
       let uu____6622 = FStar_ST.op_Bang stack  in env :: uu____6622  in
     FStar_ST.op_Colon_Equals stack uu____6619);
    (let uu___90_6671 = env  in
     let uu____6672 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____6675 = FStar_Util.smap_copy (sigtab env)  in
     let uu____6678 =
       let uu____6691 =
         let uu____6694 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____6694  in
       let uu____6719 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____6691, uu____6719)  in
     let uu____6760 =
       let uu____6763 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____6763  in
     {
       solver = (uu___90_6671.solver);
       range = (uu___90_6671.range);
       curmodule = (uu___90_6671.curmodule);
       gamma = (uu___90_6671.gamma);
       gamma_cache = uu____6672;
       modules = (uu___90_6671.modules);
       expected_typ = (uu___90_6671.expected_typ);
       sigtab = uu____6675;
       is_pattern = (uu___90_6671.is_pattern);
       instantiate_imp = (uu___90_6671.instantiate_imp);
       effects = (uu___90_6671.effects);
       generalize = (uu___90_6671.generalize);
       letrecs = (uu___90_6671.letrecs);
       top_level = (uu___90_6671.top_level);
       check_uvars = (uu___90_6671.check_uvars);
       use_eq = (uu___90_6671.use_eq);
       is_iface = (uu___90_6671.is_iface);
       admit = (uu___90_6671.admit);
       lax = (uu___90_6671.lax);
       lax_universes = (uu___90_6671.lax_universes);
       failhard = (uu___90_6671.failhard);
       nosynth = (uu___90_6671.nosynth);
       tc_term = (uu___90_6671.tc_term);
       type_of = (uu___90_6671.type_of);
       universe_of = (uu___90_6671.universe_of);
       check_type_of = (uu___90_6671.check_type_of);
       use_bv_sorts = (uu___90_6671.use_bv_sorts);
       qtbl_name_and_index = uu____6678;
       proof_ns = (uu___90_6671.proof_ns);
       synth = (uu___90_6671.synth);
       is_native_tactic = (uu___90_6671.is_native_tactic);
       identifier_info = uu____6760;
       tc_hooks = (uu___90_6671.tc_hooks);
       dsenv = (uu___90_6671.dsenv);
       dep_graph = (uu___90_6671.dep_graph)
     })
  
let (pop_stack : Prims.unit -> env) =
  fun uu____6807  ->
    let uu____6808 = FStar_ST.op_Bang stack  in
    match uu____6808 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6862 -> failwith "Impossible: Too many pops"
  
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
    | (uu____6891,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____6923 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6949  ->
                  match uu____6949 with
                  | (m,uu____6955) -> FStar_Ident.lid_equals l m))
           in
        (match uu____6923 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___91_6963 = env  in
               {
                 solver = (uu___91_6963.solver);
                 range = (uu___91_6963.range);
                 curmodule = (uu___91_6963.curmodule);
                 gamma = (uu___91_6963.gamma);
                 gamma_cache = (uu___91_6963.gamma_cache);
                 modules = (uu___91_6963.modules);
                 expected_typ = (uu___91_6963.expected_typ);
                 sigtab = (uu___91_6963.sigtab);
                 is_pattern = (uu___91_6963.is_pattern);
                 instantiate_imp = (uu___91_6963.instantiate_imp);
                 effects = (uu___91_6963.effects);
                 generalize = (uu___91_6963.generalize);
                 letrecs = (uu___91_6963.letrecs);
                 top_level = (uu___91_6963.top_level);
                 check_uvars = (uu___91_6963.check_uvars);
                 use_eq = (uu___91_6963.use_eq);
                 is_iface = (uu___91_6963.is_iface);
                 admit = (uu___91_6963.admit);
                 lax = (uu___91_6963.lax);
                 lax_universes = (uu___91_6963.lax_universes);
                 failhard = (uu___91_6963.failhard);
                 nosynth = (uu___91_6963.nosynth);
                 tc_term = (uu___91_6963.tc_term);
                 type_of = (uu___91_6963.type_of);
                 universe_of = (uu___91_6963.universe_of);
                 check_type_of = (uu___91_6963.check_type_of);
                 use_bv_sorts = (uu___91_6963.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___91_6963.proof_ns);
                 synth = (uu___91_6963.synth);
                 is_native_tactic = (uu___91_6963.is_native_tactic);
                 identifier_info = (uu___91_6963.identifier_info);
                 tc_hooks = (uu___91_6963.tc_hooks);
                 dsenv = (uu___91_6963.dsenv);
                 dep_graph = (uu___91_6963.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6976,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___92_6985 = env  in
               {
                 solver = (uu___92_6985.solver);
                 range = (uu___92_6985.range);
                 curmodule = (uu___92_6985.curmodule);
                 gamma = (uu___92_6985.gamma);
                 gamma_cache = (uu___92_6985.gamma_cache);
                 modules = (uu___92_6985.modules);
                 expected_typ = (uu___92_6985.expected_typ);
                 sigtab = (uu___92_6985.sigtab);
                 is_pattern = (uu___92_6985.is_pattern);
                 instantiate_imp = (uu___92_6985.instantiate_imp);
                 effects = (uu___92_6985.effects);
                 generalize = (uu___92_6985.generalize);
                 letrecs = (uu___92_6985.letrecs);
                 top_level = (uu___92_6985.top_level);
                 check_uvars = (uu___92_6985.check_uvars);
                 use_eq = (uu___92_6985.use_eq);
                 is_iface = (uu___92_6985.is_iface);
                 admit = (uu___92_6985.admit);
                 lax = (uu___92_6985.lax);
                 lax_universes = (uu___92_6985.lax_universes);
                 failhard = (uu___92_6985.failhard);
                 nosynth = (uu___92_6985.nosynth);
                 tc_term = (uu___92_6985.tc_term);
                 type_of = (uu___92_6985.type_of);
                 universe_of = (uu___92_6985.universe_of);
                 check_type_of = (uu___92_6985.check_type_of);
                 use_bv_sorts = (uu___92_6985.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 proof_ns = (uu___92_6985.proof_ns);
                 synth = (uu___92_6985.synth);
                 is_native_tactic = (uu___92_6985.is_native_tactic);
                 identifier_info = (uu___92_6985.identifier_info);
                 tc_hooks = (uu___92_6985.tc_hooks);
                 dsenv = (uu___92_6985.dsenv);
                 dep_graph = (uu___92_6985.dep_graph)
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
        (let uu___93_7011 = e  in
         {
           solver = (uu___93_7011.solver);
           range = r;
           curmodule = (uu___93_7011.curmodule);
           gamma = (uu___93_7011.gamma);
           gamma_cache = (uu___93_7011.gamma_cache);
           modules = (uu___93_7011.modules);
           expected_typ = (uu___93_7011.expected_typ);
           sigtab = (uu___93_7011.sigtab);
           is_pattern = (uu___93_7011.is_pattern);
           instantiate_imp = (uu___93_7011.instantiate_imp);
           effects = (uu___93_7011.effects);
           generalize = (uu___93_7011.generalize);
           letrecs = (uu___93_7011.letrecs);
           top_level = (uu___93_7011.top_level);
           check_uvars = (uu___93_7011.check_uvars);
           use_eq = (uu___93_7011.use_eq);
           is_iface = (uu___93_7011.is_iface);
           admit = (uu___93_7011.admit);
           lax = (uu___93_7011.lax);
           lax_universes = (uu___93_7011.lax_universes);
           failhard = (uu___93_7011.failhard);
           nosynth = (uu___93_7011.nosynth);
           tc_term = (uu___93_7011.tc_term);
           type_of = (uu___93_7011.type_of);
           universe_of = (uu___93_7011.universe_of);
           check_type_of = (uu___93_7011.check_type_of);
           use_bv_sorts = (uu___93_7011.use_bv_sorts);
           qtbl_name_and_index = (uu___93_7011.qtbl_name_and_index);
           proof_ns = (uu___93_7011.proof_ns);
           synth = (uu___93_7011.synth);
           is_native_tactic = (uu___93_7011.is_native_tactic);
           identifier_info = (uu___93_7011.identifier_info);
           tc_hooks = (uu___93_7011.tc_hooks);
           dsenv = (uu___93_7011.dsenv);
           dep_graph = (uu___93_7011.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> Prims.unit) =
  fun env  ->
    fun enabled  ->
      let uu____7021 =
        let uu____7022 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____7022 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7021
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____7070 =
          let uu____7071 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____7071 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7070
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____7119 =
          let uu____7120 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____7120 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____7119
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit)
  =
  fun env  ->
    fun ty_map  ->
      let uu____7170 =
        let uu____7171 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____7171 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____7170
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___94_7224 = env  in
      {
        solver = (uu___94_7224.solver);
        range = (uu___94_7224.range);
        curmodule = lid;
        gamma = (uu___94_7224.gamma);
        gamma_cache = (uu___94_7224.gamma_cache);
        modules = (uu___94_7224.modules);
        expected_typ = (uu___94_7224.expected_typ);
        sigtab = (uu___94_7224.sigtab);
        is_pattern = (uu___94_7224.is_pattern);
        instantiate_imp = (uu___94_7224.instantiate_imp);
        effects = (uu___94_7224.effects);
        generalize = (uu___94_7224.generalize);
        letrecs = (uu___94_7224.letrecs);
        top_level = (uu___94_7224.top_level);
        check_uvars = (uu___94_7224.check_uvars);
        use_eq = (uu___94_7224.use_eq);
        is_iface = (uu___94_7224.is_iface);
        admit = (uu___94_7224.admit);
        lax = (uu___94_7224.lax);
        lax_universes = (uu___94_7224.lax_universes);
        failhard = (uu___94_7224.failhard);
        nosynth = (uu___94_7224.nosynth);
        tc_term = (uu___94_7224.tc_term);
        type_of = (uu___94_7224.type_of);
        universe_of = (uu___94_7224.universe_of);
        check_type_of = (uu___94_7224.check_type_of);
        use_bv_sorts = (uu___94_7224.use_bv_sorts);
        qtbl_name_and_index = (uu___94_7224.qtbl_name_and_index);
        proof_ns = (uu___94_7224.proof_ns);
        synth = (uu___94_7224.synth);
        is_native_tactic = (uu___94_7224.is_native_tactic);
        identifier_info = (uu___94_7224.identifier_info);
        tc_hooks = (uu___94_7224.tc_hooks);
        dsenv = (uu___94_7224.dsenv);
        dep_graph = (uu___94_7224.dep_graph)
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
    let uu____7250 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____7250)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____7258 =
      let uu____7259 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____7259  in
    (FStar_Errors.Fatal_VariableNotFound, uu____7258)
  
let (new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe) =
  fun uu____7262  ->
    let uu____7263 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____7263
  
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
      | ((formals,t),uu____7301) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____7325 = FStar_Syntax_Subst.subst vs t  in (us, uu____7325)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___72_7338  ->
    match uu___72_7338 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7362  -> new_u_univ ()))
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
      let uu____7375 = inst_tscheme t  in
      match uu____7375 with
      | (us,t1) ->
          let uu____7386 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____7386)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7398  ->
          match uu____7398 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7413 =
                         let uu____7414 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____7415 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____7416 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____7417 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7414 uu____7415 uu____7416 uu____7417
                          in
                       failwith uu____7413)
                    else ();
                    (let uu____7419 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____7419))
               | uu____7426 ->
                   let uu____7427 =
                     let uu____7428 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7428
                      in
                   failwith uu____7427)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____7432 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____7436 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7440 -> false
  
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
             | ([],uu____7474) -> Maybe
             | (uu____7481,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7500 -> No  in
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
          let uu____7585 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____7585 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___73_7630  ->
                   match uu___73_7630 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7673 =
                           let uu____7692 =
                             let uu____7707 = inst_tscheme t  in
                             FStar_Util.Inl uu____7707  in
                           (uu____7692, (FStar_Ident.range_of_lid l))  in
                         FStar_Pervasives_Native.Some uu____7673
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7773,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7775);
                                     FStar_Syntax_Syntax.sigrng = uu____7776;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7777;
                                     FStar_Syntax_Syntax.sigmeta = uu____7778;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7779;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7799 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____7799
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7845 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7852 -> cache t  in
                       let uu____7853 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7853 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7928 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____7928 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____8014 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____8074 = find_in_sigtab env lid  in
         match uu____8074 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8153) ->
          add_sigelts env ses
      | uu____8162 ->
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
            | uu____8176 -> ()))

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
        (fun uu___74_8203  ->
           match uu___74_8203 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8221 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____8274,lb::[]),uu____8276) ->
            let uu____8289 =
              let uu____8298 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____8307 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____8298, uu____8307)  in
            FStar_Pervasives_Native.Some uu____8289
        | FStar_Syntax_Syntax.Sig_let ((uu____8320,lbs),uu____8322) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____8358 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____8370 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____8370
                     then
                       let uu____8381 =
                         let uu____8390 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____8399 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____8390, uu____8399)  in
                       FStar_Pervasives_Native.Some uu____8381
                     else FStar_Pervasives_Native.None)
        | uu____8421 -> FStar_Pervasives_Native.None
  
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
          let uu____8474 =
            let uu____8483 =
              let uu____8488 =
                let uu____8489 =
                  let uu____8492 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____8492
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____8489)  in
              inst_tscheme1 uu____8488  in
            (uu____8483, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8474
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____8512,uu____8513) ->
          let uu____8518 =
            let uu____8527 =
              let uu____8532 =
                let uu____8533 =
                  let uu____8536 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____8536  in
                (us, uu____8533)  in
              inst_tscheme1 uu____8532  in
            (uu____8527, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____8518
      | uu____8553 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____8631 =
          match uu____8631 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____8727,uvs,t,uu____8730,uu____8731,uu____8732);
                      FStar_Syntax_Syntax.sigrng = uu____8733;
                      FStar_Syntax_Syntax.sigquals = uu____8734;
                      FStar_Syntax_Syntax.sigmeta = uu____8735;
                      FStar_Syntax_Syntax.sigattrs = uu____8736;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8757 =
                     let uu____8766 = inst_tscheme1 (uvs, t)  in
                     (uu____8766, rng)  in
                   FStar_Pervasives_Native.Some uu____8757
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____8786;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____8788;
                      FStar_Syntax_Syntax.sigattrs = uu____8789;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____8806 =
                     let uu____8807 = in_cur_mod env l  in uu____8807 = Yes
                      in
                   if uu____8806
                   then
                     let uu____8818 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____8818
                      then
                        let uu____8831 =
                          let uu____8840 = inst_tscheme1 (uvs, t)  in
                          (uu____8840, rng)  in
                        FStar_Pervasives_Native.Some uu____8831
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____8867 =
                        let uu____8876 = inst_tscheme1 (uvs, t)  in
                        (uu____8876, rng)  in
                      FStar_Pervasives_Native.Some uu____8867)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____8897,uu____8898);
                      FStar_Syntax_Syntax.sigrng = uu____8899;
                      FStar_Syntax_Syntax.sigquals = uu____8900;
                      FStar_Syntax_Syntax.sigmeta = uu____8901;
                      FStar_Syntax_Syntax.sigattrs = uu____8902;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____8941 =
                          let uu____8950 = inst_tscheme1 (uvs, k)  in
                          (uu____8950, rng)  in
                        FStar_Pervasives_Native.Some uu____8941
                    | uu____8967 ->
                        let uu____8968 =
                          let uu____8977 =
                            let uu____8982 =
                              let uu____8983 =
                                let uu____8986 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____8986
                                 in
                              (uvs, uu____8983)  in
                            inst_tscheme1 uu____8982  in
                          (uu____8977, rng)  in
                        FStar_Pervasives_Native.Some uu____8968)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____9007,uu____9008);
                      FStar_Syntax_Syntax.sigrng = uu____9009;
                      FStar_Syntax_Syntax.sigquals = uu____9010;
                      FStar_Syntax_Syntax.sigmeta = uu____9011;
                      FStar_Syntax_Syntax.sigattrs = uu____9012;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____9052 =
                          let uu____9061 = inst_tscheme_with (uvs, k) us  in
                          (uu____9061, rng)  in
                        FStar_Pervasives_Native.Some uu____9052
                    | uu____9078 ->
                        let uu____9079 =
                          let uu____9088 =
                            let uu____9093 =
                              let uu____9094 =
                                let uu____9097 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____9097
                                 in
                              (uvs, uu____9094)  in
                            inst_tscheme_with uu____9093 us  in
                          (uu____9088, rng)  in
                        FStar_Pervasives_Native.Some uu____9079)
               | FStar_Util.Inr se ->
                   let uu____9131 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____9152;
                          FStar_Syntax_Syntax.sigrng = uu____9153;
                          FStar_Syntax_Syntax.sigquals = uu____9154;
                          FStar_Syntax_Syntax.sigmeta = uu____9155;
                          FStar_Syntax_Syntax.sigattrs = uu____9156;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____9171 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____9131
                     (FStar_Util.map_option
                        (fun uu____9219  ->
                           match uu____9219 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____9250 =
          let uu____9261 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____9261 mapper  in
        match uu____9250 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            FStar_Pervasives_Native.Some
              ((us,
                 (let uu___95_9354 = t  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___95_9354.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                    FStar_Syntax_Syntax.vars =
                      (uu___95_9354.FStar_Syntax_Syntax.vars)
                  })), r)
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____9379 = lookup_qname env l  in
      match uu____9379 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9398 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____9446 = try_lookup_bv env bv  in
      match uu____9446 with
      | FStar_Pervasives_Native.None  ->
          let uu____9461 = variable_not_found bv  in
          FStar_Errors.raise_error uu____9461 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9476 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____9477 =
            let uu____9478 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____9478  in
          (uu____9476, uu____9477)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____9495 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____9495 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____9561 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____9561  in
          let uu____9562 =
            let uu____9571 =
              let uu____9576 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____9576)  in
            (uu____9571, r1)  in
          FStar_Pervasives_Native.Some uu____9562
  
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
        let uu____9604 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____9604 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____9637,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____9662 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____9662  in
            let uu____9663 =
              let uu____9668 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____9668, r1)  in
            FStar_Pervasives_Native.Some uu____9663
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____9687 = try_lookup_lid env l  in
      match uu____9687 with
      | FStar_Pervasives_Native.None  ->
          let uu____9714 = name_not_found l  in
          FStar_Errors.raise_error uu____9714 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___75_9754  ->
              match uu___75_9754 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9756 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9771 = lookup_qname env lid  in
      match uu____9771 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9780,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9783;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9785;
              FStar_Syntax_Syntax.sigattrs = uu____9786;_},FStar_Pervasives_Native.None
            ),uu____9787)
          ->
          let uu____9836 =
            let uu____9847 =
              let uu____9852 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____9852)  in
            (uu____9847, q)  in
          FStar_Pervasives_Native.Some uu____9836
      | uu____9869 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9886 = lookup_qname env lid  in
      match uu____9886 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9891,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9894;
              FStar_Syntax_Syntax.sigquals = uu____9895;
              FStar_Syntax_Syntax.sigmeta = uu____9896;
              FStar_Syntax_Syntax.sigattrs = uu____9897;_},FStar_Pervasives_Native.None
            ),uu____9898)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9947 ->
          let uu____9948 = name_not_found lid  in
          FStar_Errors.raise_error uu____9948 (FStar_Ident.range_of_lid lid)
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____9967 = lookup_qname env lid  in
      match uu____9967 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9972,uvs,t,uu____9975,uu____9976,uu____9977);
              FStar_Syntax_Syntax.sigrng = uu____9978;
              FStar_Syntax_Syntax.sigquals = uu____9979;
              FStar_Syntax_Syntax.sigmeta = uu____9980;
              FStar_Syntax_Syntax.sigattrs = uu____9981;_},FStar_Pervasives_Native.None
            ),uu____9982)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____10035 ->
          let uu____10036 = name_not_found lid  in
          FStar_Errors.raise_error uu____10036 (FStar_Ident.range_of_lid lid)
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____10057 = lookup_qname env lid  in
      match uu____10057 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10064,uu____10065,uu____10066,uu____10067,uu____10068,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10070;
              FStar_Syntax_Syntax.sigquals = uu____10071;
              FStar_Syntax_Syntax.sigmeta = uu____10072;
              FStar_Syntax_Syntax.sigattrs = uu____10073;_},uu____10074),uu____10075)
          -> (true, dcs)
      | uu____10136 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____10145 = lookup_qname env lid  in
      match uu____10145 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10146,uu____10147,uu____10148,l,uu____10150,uu____10151);
              FStar_Syntax_Syntax.sigrng = uu____10152;
              FStar_Syntax_Syntax.sigquals = uu____10153;
              FStar_Syntax_Syntax.sigmeta = uu____10154;
              FStar_Syntax_Syntax.sigattrs = uu____10155;_},uu____10156),uu____10157)
          -> l
      | uu____10212 ->
          let uu____10213 =
            let uu____10214 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____10214  in
          failwith uu____10213
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10255)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10306,lbs),uu____10308)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____10336 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____10336
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10368 -> FStar_Pervasives_Native.None)
        | uu____10373 -> FStar_Pervasives_Native.None
  
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
        let uu____10397 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____10397
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____10420),uu____10421) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____10470 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____10487 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____10487
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____10502 = lookup_qname env ftv  in
      match uu____10502 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10506) ->
          let uu____10551 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____10551 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10572,t),r) ->
               let uu____10587 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               FStar_Pervasives_Native.Some uu____10587)
      | uu____10588 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____10595 = try_lookup_effect_lid env ftv  in
      match uu____10595 with
      | FStar_Pervasives_Native.None  ->
          let uu____10598 = name_not_found ftv  in
          FStar_Errors.raise_error uu____10598 (FStar_Ident.range_of_lid ftv)
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
        let uu____10619 = lookup_qname env lid0  in
        match uu____10619 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10630);
                FStar_Syntax_Syntax.sigrng = uu____10631;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10633;
                FStar_Syntax_Syntax.sigattrs = uu____10634;_},FStar_Pervasives_Native.None
              ),uu____10635)
            ->
            let lid1 =
              let uu____10689 =
                let uu____10690 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0)  in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10690
                 in
              FStar_Ident.set_lid_range lid uu____10689  in
            let uu____10691 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___76_10695  ->
                      match uu___76_10695 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10696 -> false))
               in
            if uu____10691
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10710 =
                      let uu____10711 =
                        let uu____10712 = get_range env  in
                        FStar_Range.string_of_range uu____10712  in
                      let uu____10713 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____10714 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10711 uu____10713 uu____10714
                       in
                    failwith uu____10710)
                  in
               match (binders, univs1) with
               | ([],uu____10721) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10738,uu____10739::uu____10740::uu____10741) ->
                   let uu____10746 =
                     let uu____10747 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____10748 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10747 uu____10748
                      in
                   failwith uu____10746
               | uu____10755 ->
                   let uu____10760 =
                     let uu____10765 =
                       let uu____10766 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____10766)  in
                     inst_tscheme_with uu____10765 insts  in
                   (match uu____10760 with
                    | (uu____10777,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____10780 =
                          let uu____10781 = FStar_Syntax_Subst.compress t1
                             in
                          uu____10781.FStar_Syntax_Syntax.n  in
                        (match uu____10780 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10828 -> failwith "Impossible")))
        | uu____10835 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10855 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____10855 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10868,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____10875 = find1 l2  in
            (match uu____10875 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____10882 = FStar_Util.smap_try_find cache l.FStar_Ident.str
           in
        match uu____10882 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10886 = find1 l  in
            (match uu____10886 with
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
      let uu____10900 = lookup_qname env l1  in
      match uu____10900 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10903;
              FStar_Syntax_Syntax.sigrng = uu____10904;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10906;
              FStar_Syntax_Syntax.sigattrs = uu____10907;_},uu____10908),uu____10909)
          -> q
      | uu____10960 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10973 =
          let uu____10974 =
            let uu____10975 = FStar_Util.string_of_int i  in
            let uu____10976 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10975 uu____10976
             in
          failwith uu____10974  in
        let uu____10977 = lookup_datacon env lid  in
        match uu____10977 with
        | (uu____10982,t) ->
            let uu____10984 =
              let uu____10985 = FStar_Syntax_Subst.compress t  in
              uu____10985.FStar_Syntax_Syntax.n  in
            (match uu____10984 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10989) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____11020 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____11020
                      FStar_Pervasives_Native.fst)
             | uu____11029 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11036 = lookup_qname env l  in
      match uu____11036 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11037,uu____11038,uu____11039);
              FStar_Syntax_Syntax.sigrng = uu____11040;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11042;
              FStar_Syntax_Syntax.sigattrs = uu____11043;_},uu____11044),uu____11045)
          ->
          FStar_Util.for_some
            (fun uu___77_11098  ->
               match uu___77_11098 with
               | FStar_Syntax_Syntax.Projector uu____11099 -> true
               | uu____11104 -> false) quals
      | uu____11105 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11112 = lookup_qname env lid  in
      match uu____11112 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11113,uu____11114,uu____11115,uu____11116,uu____11117,uu____11118);
              FStar_Syntax_Syntax.sigrng = uu____11119;
              FStar_Syntax_Syntax.sigquals = uu____11120;
              FStar_Syntax_Syntax.sigmeta = uu____11121;
              FStar_Syntax_Syntax.sigattrs = uu____11122;_},uu____11123),uu____11124)
          -> true
      | uu____11179 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11186 = lookup_qname env lid  in
      match uu____11186 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11187,uu____11188,uu____11189,uu____11190,uu____11191,uu____11192);
              FStar_Syntax_Syntax.sigrng = uu____11193;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11195;
              FStar_Syntax_Syntax.sigattrs = uu____11196;_},uu____11197),uu____11198)
          ->
          FStar_Util.for_some
            (fun uu___78_11259  ->
               match uu___78_11259 with
               | FStar_Syntax_Syntax.RecordType uu____11260 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11269 -> true
               | uu____11278 -> false) quals
      | uu____11279 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____11283,uu____11284);
            FStar_Syntax_Syntax.sigrng = uu____11285;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____11287;
            FStar_Syntax_Syntax.sigattrs = uu____11288;_},uu____11289),uu____11290)
        ->
        FStar_Util.for_some
          (fun uu___79_11347  ->
             match uu___79_11347 with
             | FStar_Syntax_Syntax.Action uu____11348 -> true
             | uu____11349 -> false) quals
    | uu____11350 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____11357 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____11357
  
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
      let uu____11367 =
        let uu____11368 = FStar_Syntax_Util.un_uinst head1  in
        uu____11368.FStar_Syntax_Syntax.n  in
      match uu____11367 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11372 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11379 = lookup_qname env l  in
      match uu____11379 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11381),uu____11382) ->
          FStar_Util.for_some
            (fun uu___80_11430  ->
               match uu___80_11430 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11431 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11432 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11497 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11513) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11530 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11537 ->
                 FStar_Pervasives_Native.Some true
             | uu____11554 -> FStar_Pervasives_Native.Some false)
         in
      let uu____11555 =
        let uu____11558 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____11558 mapper  in
      match uu____11555 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____11604 = lookup_qname env lid  in
      match uu____11604 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11605,uu____11606,tps,uu____11608,uu____11609,uu____11610);
              FStar_Syntax_Syntax.sigrng = uu____11611;
              FStar_Syntax_Syntax.sigquals = uu____11612;
              FStar_Syntax_Syntax.sigmeta = uu____11613;
              FStar_Syntax_Syntax.sigattrs = uu____11614;_},uu____11615),uu____11616)
          -> FStar_List.length tps
      | uu____11679 ->
          let uu____11680 = name_not_found lid  in
          FStar_Errors.raise_error uu____11680 (FStar_Ident.range_of_lid lid)
  
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
           (fun uu____11724  ->
              match uu____11724 with
              | (d,uu____11732) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____11743 = effect_decl_opt env l  in
      match uu____11743 with
      | FStar_Pervasives_Native.None  ->
          let uu____11758 = name_not_found l  in
          FStar_Errors.raise_error uu____11758 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____11784  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11799  ->
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
            (let uu____11832 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11885  ->
                       match uu____11885 with
                       | (m1,m2,uu____11898,uu____11899,uu____11900) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____11832 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11917 =
                   let uu____11922 =
                     let uu____11923 = FStar_Syntax_Print.lid_to_string l1
                        in
                     let uu____11924 = FStar_Syntax_Print.lid_to_string l2
                        in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11923
                       uu____11924
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____11922)
                    in
                 FStar_Errors.raise_error uu____11917 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11931,uu____11932,m3,j1,j2) -> (m3, j1, j2))
  
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
  'Auu____11969 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11969)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11996 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12022  ->
                match uu____12022 with
                | (d,uu____12028) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____11996 with
      | FStar_Pervasives_Native.None  ->
          let uu____12039 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____12039
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12052 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____12052 with
           | (uu____12063,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12073)::(wp,uu____12075)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12111 -> failwith "Impossible"))
  
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
                 let uu____12154 = get_range env  in
                 let uu____12155 =
                   let uu____12158 =
                     let uu____12159 =
                       let uu____12174 =
                         let uu____12177 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____12177]  in
                       (null_wp, uu____12174)  in
                     FStar_Syntax_Syntax.Tm_app uu____12159  in
                   FStar_Syntax_Syntax.mk uu____12158  in
                 uu____12155 FStar_Pervasives_Native.None uu____12154  in
               let uu____12183 =
                 let uu____12184 =
                   let uu____12193 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____12193]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12184;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____12183)
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___96_12202 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___96_12202.order);
              joins = (uu___96_12202.joins)
            }  in
          let uu___97_12211 = env  in
          {
            solver = (uu___97_12211.solver);
            range = (uu___97_12211.range);
            curmodule = (uu___97_12211.curmodule);
            gamma = (uu___97_12211.gamma);
            gamma_cache = (uu___97_12211.gamma_cache);
            modules = (uu___97_12211.modules);
            expected_typ = (uu___97_12211.expected_typ);
            sigtab = (uu___97_12211.sigtab);
            is_pattern = (uu___97_12211.is_pattern);
            instantiate_imp = (uu___97_12211.instantiate_imp);
            effects;
            generalize = (uu___97_12211.generalize);
            letrecs = (uu___97_12211.letrecs);
            top_level = (uu___97_12211.top_level);
            check_uvars = (uu___97_12211.check_uvars);
            use_eq = (uu___97_12211.use_eq);
            is_iface = (uu___97_12211.is_iface);
            admit = (uu___97_12211.admit);
            lax = (uu___97_12211.lax);
            lax_universes = (uu___97_12211.lax_universes);
            failhard = (uu___97_12211.failhard);
            nosynth = (uu___97_12211.nosynth);
            tc_term = (uu___97_12211.tc_term);
            type_of = (uu___97_12211.type_of);
            universe_of = (uu___97_12211.universe_of);
            check_type_of = (uu___97_12211.check_type_of);
            use_bv_sorts = (uu___97_12211.use_bv_sorts);
            qtbl_name_and_index = (uu___97_12211.qtbl_name_and_index);
            proof_ns = (uu___97_12211.proof_ns);
            synth = (uu___97_12211.synth);
            is_native_tactic = (uu___97_12211.is_native_tactic);
            identifier_info = (uu___97_12211.identifier_info);
            tc_hooks = (uu___97_12211.tc_hooks);
            dsenv = (uu___97_12211.dsenv);
            dep_graph = (uu___97_12211.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12231 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____12231  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12345 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____12346 = l1 u t wp e  in
                                l2 u t uu____12345 uu____12346))
                | uu____12347 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12395 = inst_tscheme_with lift_t [u]  in
            match uu____12395 with
            | (uu____12402,lift_t1) ->
                let uu____12404 =
                  let uu____12407 =
                    let uu____12408 =
                      let uu____12423 =
                        let uu____12426 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12427 =
                          let uu____12430 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____12430]  in
                        uu____12426 :: uu____12427  in
                      (lift_t1, uu____12423)  in
                    FStar_Syntax_Syntax.Tm_app uu____12408  in
                  FStar_Syntax_Syntax.mk uu____12407  in
                uu____12404 FStar_Pervasives_Native.None
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
            let uu____12480 = inst_tscheme_with lift_t [u]  in
            match uu____12480 with
            | (uu____12487,lift_t1) ->
                let uu____12489 =
                  let uu____12492 =
                    let uu____12493 =
                      let uu____12508 =
                        let uu____12511 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____12512 =
                          let uu____12515 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____12516 =
                            let uu____12519 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____12519]  in
                          uu____12515 :: uu____12516  in
                        uu____12511 :: uu____12512  in
                      (lift_t1, uu____12508)  in
                    FStar_Syntax_Syntax.Tm_app uu____12493  in
                  FStar_Syntax_Syntax.mk uu____12492  in
                uu____12489 FStar_Pervasives_Native.None
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
              let uu____12561 =
                let uu____12562 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____12562
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____12561  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____12566 =
              let uu____12567 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____12567  in
            let uu____12568 =
              let uu____12569 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12591 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____12591)
                 in
              FStar_Util.dflt "none" uu____12569  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12566
              uu____12568
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12617  ->
                    match uu____12617 with
                    | (e,uu____12625) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____12644 =
            match uu____12644 with
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
              let uu____12682 =
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
                                    (let uu____12703 =
                                       let uu____12712 =
                                         find_edge order1 (i, k)  in
                                       let uu____12715 =
                                         find_edge order1 (k, j)  in
                                       (uu____12712, uu____12715)  in
                                     match uu____12703 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12730 =
                                           compose_edges e1 e2  in
                                         [uu____12730]
                                     | uu____12731 -> [])))))
                 in
              FStar_List.append order1 uu____12682  in
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
                   let uu____12761 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12763 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____12763
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____12761
                   then
                     let uu____12768 =
                       let uu____12773 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12773)
                        in
                     let uu____12774 = get_range env  in
                     FStar_Errors.raise_error uu____12768 uu____12774
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
                                            let uu____12899 =
                                              let uu____12908 =
                                                find_edge order2 (i, k)  in
                                              let uu____12911 =
                                                find_edge order2 (j, k)  in
                                              (uu____12908, uu____12911)  in
                                            match uu____12899 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12953,uu____12954)
                                                     ->
                                                     let uu____12961 =
                                                       let uu____12966 =
                                                         let uu____12967 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12967
                                                          in
                                                       let uu____12970 =
                                                         let uu____12971 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____12971
                                                          in
                                                       (uu____12966,
                                                         uu____12970)
                                                        in
                                                     (match uu____12961 with
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
                                            | uu____13006 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___98_13079 = env.effects  in
              { decls = (uu___98_13079.decls); order = order2; joins }  in
            let uu___99_13080 = env  in
            {
              solver = (uu___99_13080.solver);
              range = (uu___99_13080.range);
              curmodule = (uu___99_13080.curmodule);
              gamma = (uu___99_13080.gamma);
              gamma_cache = (uu___99_13080.gamma_cache);
              modules = (uu___99_13080.modules);
              expected_typ = (uu___99_13080.expected_typ);
              sigtab = (uu___99_13080.sigtab);
              is_pattern = (uu___99_13080.is_pattern);
              instantiate_imp = (uu___99_13080.instantiate_imp);
              effects;
              generalize = (uu___99_13080.generalize);
              letrecs = (uu___99_13080.letrecs);
              top_level = (uu___99_13080.top_level);
              check_uvars = (uu___99_13080.check_uvars);
              use_eq = (uu___99_13080.use_eq);
              is_iface = (uu___99_13080.is_iface);
              admit = (uu___99_13080.admit);
              lax = (uu___99_13080.lax);
              lax_universes = (uu___99_13080.lax_universes);
              failhard = (uu___99_13080.failhard);
              nosynth = (uu___99_13080.nosynth);
              tc_term = (uu___99_13080.tc_term);
              type_of = (uu___99_13080.type_of);
              universe_of = (uu___99_13080.universe_of);
              check_type_of = (uu___99_13080.check_type_of);
              use_bv_sorts = (uu___99_13080.use_bv_sorts);
              qtbl_name_and_index = (uu___99_13080.qtbl_name_and_index);
              proof_ns = (uu___99_13080.proof_ns);
              synth = (uu___99_13080.synth);
              is_native_tactic = (uu___99_13080.is_native_tactic);
              identifier_info = (uu___99_13080.identifier_info);
              tc_hooks = (uu___99_13080.tc_hooks);
              dsenv = (uu___99_13080.dsenv);
              dep_graph = (uu___99_13080.dep_graph)
            }))
      | uu____13081 -> env
  
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
        | uu____13105 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____13113 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____13113 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13130 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____13130 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13148 =
                     let uu____13153 =
                       let uu____13154 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____13159 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____13166 =
                         let uu____13167 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____13167  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13154 uu____13159 uu____13166
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____13153)
                      in
                   FStar_Errors.raise_error uu____13148
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13172 =
                     let uu____13181 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____13181 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____13198  ->
                        fun uu____13199  ->
                          match (uu____13198, uu____13199) with
                          | ((x,uu____13221),(t,uu____13223)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13172
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____13242 =
                     let uu___100_13243 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___100_13243.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___100_13243.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___100_13243.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___100_13243.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____13242
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
          let uu____13265 = effect_decl_opt env effect_name  in
          match uu____13265 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13298 =
                only_reifiable &&
                  (let uu____13300 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____13300)
                 in
              if uu____13298
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13316 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13335 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____13364 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____13364
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____13365 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13365
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____13375 =
                       let uu____13378 = get_range env  in
                       let uu____13379 =
                         let uu____13382 =
                           let uu____13383 =
                             let uu____13398 =
                               let uu____13401 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____13401; wp]  in
                             (repr, uu____13398)  in
                           FStar_Syntax_Syntax.Tm_app uu____13383  in
                         FStar_Syntax_Syntax.mk uu____13382  in
                       uu____13379 FStar_Pervasives_Native.None uu____13378
                        in
                     FStar_Pervasives_Native.Some uu____13375)
  
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
          let uu____13447 =
            let uu____13452 =
              let uu____13453 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13453
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13452)  in
          let uu____13454 = get_range env  in
          FStar_Errors.raise_error uu____13447 uu____13454  in
        let uu____13455 = effect_repr_aux true env c u_c  in
        match uu____13455 with
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
      | uu____13489 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____13496 =
        let uu____13497 = FStar_Syntax_Subst.compress t  in
        uu____13497.FStar_Syntax_Syntax.n  in
      match uu____13496 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13500,c) ->
          is_reifiable_comp env c
      | uu____13518 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13540)::uu____13541 -> x :: rest
        | (Binding_sig_inst uu____13550)::uu____13551 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13566 = push1 x rest1  in local :: uu____13566
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___101_13570 = env  in
       let uu____13571 = push1 s env.gamma  in
       {
         solver = (uu___101_13570.solver);
         range = (uu___101_13570.range);
         curmodule = (uu___101_13570.curmodule);
         gamma = uu____13571;
         gamma_cache = (uu___101_13570.gamma_cache);
         modules = (uu___101_13570.modules);
         expected_typ = (uu___101_13570.expected_typ);
         sigtab = (uu___101_13570.sigtab);
         is_pattern = (uu___101_13570.is_pattern);
         instantiate_imp = (uu___101_13570.instantiate_imp);
         effects = (uu___101_13570.effects);
         generalize = (uu___101_13570.generalize);
         letrecs = (uu___101_13570.letrecs);
         top_level = (uu___101_13570.top_level);
         check_uvars = (uu___101_13570.check_uvars);
         use_eq = (uu___101_13570.use_eq);
         is_iface = (uu___101_13570.is_iface);
         admit = (uu___101_13570.admit);
         lax = (uu___101_13570.lax);
         lax_universes = (uu___101_13570.lax_universes);
         failhard = (uu___101_13570.failhard);
         nosynth = (uu___101_13570.nosynth);
         tc_term = (uu___101_13570.tc_term);
         type_of = (uu___101_13570.type_of);
         universe_of = (uu___101_13570.universe_of);
         check_type_of = (uu___101_13570.check_type_of);
         use_bv_sorts = (uu___101_13570.use_bv_sorts);
         qtbl_name_and_index = (uu___101_13570.qtbl_name_and_index);
         proof_ns = (uu___101_13570.proof_ns);
         synth = (uu___101_13570.synth);
         is_native_tactic = (uu___101_13570.is_native_tactic);
         identifier_info = (uu___101_13570.identifier_info);
         tc_hooks = (uu___101_13570.tc_hooks);
         dsenv = (uu___101_13570.dsenv);
         dep_graph = (uu___101_13570.dep_graph)
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
      let uu___102_13601 = env  in
      {
        solver = (uu___102_13601.solver);
        range = (uu___102_13601.range);
        curmodule = (uu___102_13601.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___102_13601.gamma_cache);
        modules = (uu___102_13601.modules);
        expected_typ = (uu___102_13601.expected_typ);
        sigtab = (uu___102_13601.sigtab);
        is_pattern = (uu___102_13601.is_pattern);
        instantiate_imp = (uu___102_13601.instantiate_imp);
        effects = (uu___102_13601.effects);
        generalize = (uu___102_13601.generalize);
        letrecs = (uu___102_13601.letrecs);
        top_level = (uu___102_13601.top_level);
        check_uvars = (uu___102_13601.check_uvars);
        use_eq = (uu___102_13601.use_eq);
        is_iface = (uu___102_13601.is_iface);
        admit = (uu___102_13601.admit);
        lax = (uu___102_13601.lax);
        lax_universes = (uu___102_13601.lax_universes);
        failhard = (uu___102_13601.failhard);
        nosynth = (uu___102_13601.nosynth);
        tc_term = (uu___102_13601.tc_term);
        type_of = (uu___102_13601.type_of);
        universe_of = (uu___102_13601.universe_of);
        check_type_of = (uu___102_13601.check_type_of);
        use_bv_sorts = (uu___102_13601.use_bv_sorts);
        qtbl_name_and_index = (uu___102_13601.qtbl_name_and_index);
        proof_ns = (uu___102_13601.proof_ns);
        synth = (uu___102_13601.synth);
        is_native_tactic = (uu___102_13601.is_native_tactic);
        identifier_info = (uu___102_13601.identifier_info);
        tc_hooks = (uu___102_13601.tc_hooks);
        dsenv = (uu___102_13601.dsenv);
        dep_graph = (uu___102_13601.dep_graph)
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
            (let uu___103_13632 = env  in
             {
               solver = (uu___103_13632.solver);
               range = (uu___103_13632.range);
               curmodule = (uu___103_13632.curmodule);
               gamma = rest;
               gamma_cache = (uu___103_13632.gamma_cache);
               modules = (uu___103_13632.modules);
               expected_typ = (uu___103_13632.expected_typ);
               sigtab = (uu___103_13632.sigtab);
               is_pattern = (uu___103_13632.is_pattern);
               instantiate_imp = (uu___103_13632.instantiate_imp);
               effects = (uu___103_13632.effects);
               generalize = (uu___103_13632.generalize);
               letrecs = (uu___103_13632.letrecs);
               top_level = (uu___103_13632.top_level);
               check_uvars = (uu___103_13632.check_uvars);
               use_eq = (uu___103_13632.use_eq);
               is_iface = (uu___103_13632.is_iface);
               admit = (uu___103_13632.admit);
               lax = (uu___103_13632.lax);
               lax_universes = (uu___103_13632.lax_universes);
               failhard = (uu___103_13632.failhard);
               nosynth = (uu___103_13632.nosynth);
               tc_term = (uu___103_13632.tc_term);
               type_of = (uu___103_13632.type_of);
               universe_of = (uu___103_13632.universe_of);
               check_type_of = (uu___103_13632.check_type_of);
               use_bv_sorts = (uu___103_13632.use_bv_sorts);
               qtbl_name_and_index = (uu___103_13632.qtbl_name_and_index);
               proof_ns = (uu___103_13632.proof_ns);
               synth = (uu___103_13632.synth);
               is_native_tactic = (uu___103_13632.is_native_tactic);
               identifier_info = (uu___103_13632.identifier_info);
               tc_hooks = (uu___103_13632.tc_hooks);
               dsenv = (uu___103_13632.dsenv);
               dep_graph = (uu___103_13632.dep_graph)
             }))
    | uu____13633 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13655  ->
             match uu____13655 with | (x,uu____13661) -> push_bv env1 x) env
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
            let uu___104_13689 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___104_13689.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___104_13689.FStar_Syntax_Syntax.index);
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
      (let uu___105_13719 = env  in
       {
         solver = (uu___105_13719.solver);
         range = (uu___105_13719.range);
         curmodule = (uu___105_13719.curmodule);
         gamma = [];
         gamma_cache = (uu___105_13719.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___105_13719.sigtab);
         is_pattern = (uu___105_13719.is_pattern);
         instantiate_imp = (uu___105_13719.instantiate_imp);
         effects = (uu___105_13719.effects);
         generalize = (uu___105_13719.generalize);
         letrecs = (uu___105_13719.letrecs);
         top_level = (uu___105_13719.top_level);
         check_uvars = (uu___105_13719.check_uvars);
         use_eq = (uu___105_13719.use_eq);
         is_iface = (uu___105_13719.is_iface);
         admit = (uu___105_13719.admit);
         lax = (uu___105_13719.lax);
         lax_universes = (uu___105_13719.lax_universes);
         failhard = (uu___105_13719.failhard);
         nosynth = (uu___105_13719.nosynth);
         tc_term = (uu___105_13719.tc_term);
         type_of = (uu___105_13719.type_of);
         universe_of = (uu___105_13719.universe_of);
         check_type_of = (uu___105_13719.check_type_of);
         use_bv_sorts = (uu___105_13719.use_bv_sorts);
         qtbl_name_and_index = (uu___105_13719.qtbl_name_and_index);
         proof_ns = (uu___105_13719.proof_ns);
         synth = (uu___105_13719.synth);
         is_native_tactic = (uu___105_13719.is_native_tactic);
         identifier_info = (uu___105_13719.identifier_info);
         tc_hooks = (uu___105_13719.tc_hooks);
         dsenv = (uu___105_13719.dsenv);
         dep_graph = (uu___105_13719.dep_graph)
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
        let uu____13751 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____13751 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____13779 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____13779)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___106_13792 = env  in
      {
        solver = (uu___106_13792.solver);
        range = (uu___106_13792.range);
        curmodule = (uu___106_13792.curmodule);
        gamma = (uu___106_13792.gamma);
        gamma_cache = (uu___106_13792.gamma_cache);
        modules = (uu___106_13792.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___106_13792.sigtab);
        is_pattern = (uu___106_13792.is_pattern);
        instantiate_imp = (uu___106_13792.instantiate_imp);
        effects = (uu___106_13792.effects);
        generalize = (uu___106_13792.generalize);
        letrecs = (uu___106_13792.letrecs);
        top_level = (uu___106_13792.top_level);
        check_uvars = (uu___106_13792.check_uvars);
        use_eq = false;
        is_iface = (uu___106_13792.is_iface);
        admit = (uu___106_13792.admit);
        lax = (uu___106_13792.lax);
        lax_universes = (uu___106_13792.lax_universes);
        failhard = (uu___106_13792.failhard);
        nosynth = (uu___106_13792.nosynth);
        tc_term = (uu___106_13792.tc_term);
        type_of = (uu___106_13792.type_of);
        universe_of = (uu___106_13792.universe_of);
        check_type_of = (uu___106_13792.check_type_of);
        use_bv_sorts = (uu___106_13792.use_bv_sorts);
        qtbl_name_and_index = (uu___106_13792.qtbl_name_and_index);
        proof_ns = (uu___106_13792.proof_ns);
        synth = (uu___106_13792.synth);
        is_native_tactic = (uu___106_13792.is_native_tactic);
        identifier_info = (uu___106_13792.identifier_info);
        tc_hooks = (uu___106_13792.tc_hooks);
        dsenv = (uu___106_13792.dsenv);
        dep_graph = (uu___106_13792.dep_graph)
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
    let uu____13816 = expected_typ env_  in
    ((let uu___107_13822 = env_  in
      {
        solver = (uu___107_13822.solver);
        range = (uu___107_13822.range);
        curmodule = (uu___107_13822.curmodule);
        gamma = (uu___107_13822.gamma);
        gamma_cache = (uu___107_13822.gamma_cache);
        modules = (uu___107_13822.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___107_13822.sigtab);
        is_pattern = (uu___107_13822.is_pattern);
        instantiate_imp = (uu___107_13822.instantiate_imp);
        effects = (uu___107_13822.effects);
        generalize = (uu___107_13822.generalize);
        letrecs = (uu___107_13822.letrecs);
        top_level = (uu___107_13822.top_level);
        check_uvars = (uu___107_13822.check_uvars);
        use_eq = false;
        is_iface = (uu___107_13822.is_iface);
        admit = (uu___107_13822.admit);
        lax = (uu___107_13822.lax);
        lax_universes = (uu___107_13822.lax_universes);
        failhard = (uu___107_13822.failhard);
        nosynth = (uu___107_13822.nosynth);
        tc_term = (uu___107_13822.tc_term);
        type_of = (uu___107_13822.type_of);
        universe_of = (uu___107_13822.universe_of);
        check_type_of = (uu___107_13822.check_type_of);
        use_bv_sorts = (uu___107_13822.use_bv_sorts);
        qtbl_name_and_index = (uu___107_13822.qtbl_name_and_index);
        proof_ns = (uu___107_13822.proof_ns);
        synth = (uu___107_13822.synth);
        is_native_tactic = (uu___107_13822.is_native_tactic);
        identifier_info = (uu___107_13822.identifier_info);
        tc_hooks = (uu___107_13822.tc_hooks);
        dsenv = (uu___107_13822.dsenv);
        dep_graph = (uu___107_13822.dep_graph)
      }), uu____13816)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13835 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___81_13845  ->
                    match uu___81_13845 with
                    | Binding_sig (uu____13848,se) -> [se]
                    | uu____13854 -> []))
             in
          FStar_All.pipe_right uu____13835 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___108_13861 = env  in
       {
         solver = (uu___108_13861.solver);
         range = (uu___108_13861.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___108_13861.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___108_13861.expected_typ);
         sigtab = (uu___108_13861.sigtab);
         is_pattern = (uu___108_13861.is_pattern);
         instantiate_imp = (uu___108_13861.instantiate_imp);
         effects = (uu___108_13861.effects);
         generalize = (uu___108_13861.generalize);
         letrecs = (uu___108_13861.letrecs);
         top_level = (uu___108_13861.top_level);
         check_uvars = (uu___108_13861.check_uvars);
         use_eq = (uu___108_13861.use_eq);
         is_iface = (uu___108_13861.is_iface);
         admit = (uu___108_13861.admit);
         lax = (uu___108_13861.lax);
         lax_universes = (uu___108_13861.lax_universes);
         failhard = (uu___108_13861.failhard);
         nosynth = (uu___108_13861.nosynth);
         tc_term = (uu___108_13861.tc_term);
         type_of = (uu___108_13861.type_of);
         universe_of = (uu___108_13861.universe_of);
         check_type_of = (uu___108_13861.check_type_of);
         use_bv_sorts = (uu___108_13861.use_bv_sorts);
         qtbl_name_and_index = (uu___108_13861.qtbl_name_and_index);
         proof_ns = (uu___108_13861.proof_ns);
         synth = (uu___108_13861.synth);
         is_native_tactic = (uu___108_13861.is_native_tactic);
         identifier_info = (uu___108_13861.identifier_info);
         tc_hooks = (uu___108_13861.tc_hooks);
         dsenv = (uu___108_13861.dsenv);
         dep_graph = (uu___108_13861.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13942)::tl1 -> aux out tl1
      | (Binding_lid (uu____13946,(uu____13947,t)))::tl1 ->
          let uu____13962 =
            let uu____13969 = FStar_Syntax_Free.uvars t  in
            ext out uu____13969  in
          aux uu____13962 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13976;
            FStar_Syntax_Syntax.index = uu____13977;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13984 =
            let uu____13991 = FStar_Syntax_Free.uvars t  in
            ext out uu____13991  in
          aux uu____13984 tl1
      | (Binding_sig uu____13998)::uu____13999 -> out
      | (Binding_sig_inst uu____14008)::uu____14009 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14064)::tl1 -> aux out tl1
      | (Binding_univ uu____14076)::tl1 -> aux out tl1
      | (Binding_lid (uu____14080,(uu____14081,t)))::tl1 ->
          let uu____14096 =
            let uu____14099 = FStar_Syntax_Free.univs t  in
            ext out uu____14099  in
          aux uu____14096 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14102;
            FStar_Syntax_Syntax.index = uu____14103;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14110 =
            let uu____14113 = FStar_Syntax_Free.univs t  in
            ext out uu____14113  in
          aux uu____14110 tl1
      | (Binding_sig uu____14116)::uu____14117 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.fifo_set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14170)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14186 = FStar_Util.fifo_set_add uname out  in
          aux uu____14186 tl1
      | (Binding_lid (uu____14189,(uu____14190,t)))::tl1 ->
          let uu____14205 =
            let uu____14208 = FStar_Syntax_Free.univnames t  in
            ext out uu____14208  in
          aux uu____14205 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14211;
            FStar_Syntax_Syntax.index = uu____14212;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14219 =
            let uu____14222 = FStar_Syntax_Free.univnames t  in
            ext out uu____14222  in
          aux uu____14219 tl1
      | (Binding_sig uu____14225)::uu____14226 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___82_14250  ->
            match uu___82_14250 with
            | Binding_var x -> [x]
            | Binding_lid uu____14254 -> []
            | Binding_sig uu____14259 -> []
            | Binding_univ uu____14266 -> []
            | Binding_sig_inst uu____14267 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____14283 =
      let uu____14286 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____14286
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____14283 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> Prims.unit) =
  fun env  ->
    let uu____14308 =
      let uu____14309 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___83_14319  ->
                match uu___83_14319 with
                | Binding_var x ->
                    let uu____14321 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____14321
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14324) ->
                    let uu____14325 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____14325
                | Binding_sig (ls,uu____14327) ->
                    let uu____14332 =
                      let uu____14333 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14333
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____14332
                | Binding_sig_inst (ls,uu____14343,uu____14344) ->
                    let uu____14349 =
                      let uu____14350 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____14350
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____14349))
         in
      FStar_All.pipe_right uu____14309 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____14308 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____14367 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____14367
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14395  ->
                 fun uu____14396  ->
                   match (uu____14395, uu____14396) with
                   | ((b1,uu____14414),(b2,uu____14416)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___84_14458  ->
    match uu___84_14458 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14459 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___85_14477  ->
             match uu___85_14477 with
             | Binding_sig (lids,uu____14483) -> FStar_List.append lids keys
             | uu____14488 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14494  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14528) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14547,uu____14548) -> false  in
      let uu____14557 =
        FStar_List.tryFind
          (fun uu____14575  ->
             match uu____14575 with | (p,uu____14583) -> list_prefix p path)
          env.proof_ns
         in
      match uu____14557 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14594,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14612 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____14612
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___109_14624 = e  in
        {
          solver = (uu___109_14624.solver);
          range = (uu___109_14624.range);
          curmodule = (uu___109_14624.curmodule);
          gamma = (uu___109_14624.gamma);
          gamma_cache = (uu___109_14624.gamma_cache);
          modules = (uu___109_14624.modules);
          expected_typ = (uu___109_14624.expected_typ);
          sigtab = (uu___109_14624.sigtab);
          is_pattern = (uu___109_14624.is_pattern);
          instantiate_imp = (uu___109_14624.instantiate_imp);
          effects = (uu___109_14624.effects);
          generalize = (uu___109_14624.generalize);
          letrecs = (uu___109_14624.letrecs);
          top_level = (uu___109_14624.top_level);
          check_uvars = (uu___109_14624.check_uvars);
          use_eq = (uu___109_14624.use_eq);
          is_iface = (uu___109_14624.is_iface);
          admit = (uu___109_14624.admit);
          lax = (uu___109_14624.lax);
          lax_universes = (uu___109_14624.lax_universes);
          failhard = (uu___109_14624.failhard);
          nosynth = (uu___109_14624.nosynth);
          tc_term = (uu___109_14624.tc_term);
          type_of = (uu___109_14624.type_of);
          universe_of = (uu___109_14624.universe_of);
          check_type_of = (uu___109_14624.check_type_of);
          use_bv_sorts = (uu___109_14624.use_bv_sorts);
          qtbl_name_and_index = (uu___109_14624.qtbl_name_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___109_14624.synth);
          is_native_tactic = (uu___109_14624.is_native_tactic);
          identifier_info = (uu___109_14624.identifier_info);
          tc_hooks = (uu___109_14624.tc_hooks);
          dsenv = (uu___109_14624.dsenv);
          dep_graph = (uu___109_14624.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___110_14650 = e  in
      {
        solver = (uu___110_14650.solver);
        range = (uu___110_14650.range);
        curmodule = (uu___110_14650.curmodule);
        gamma = (uu___110_14650.gamma);
        gamma_cache = (uu___110_14650.gamma_cache);
        modules = (uu___110_14650.modules);
        expected_typ = (uu___110_14650.expected_typ);
        sigtab = (uu___110_14650.sigtab);
        is_pattern = (uu___110_14650.is_pattern);
        instantiate_imp = (uu___110_14650.instantiate_imp);
        effects = (uu___110_14650.effects);
        generalize = (uu___110_14650.generalize);
        letrecs = (uu___110_14650.letrecs);
        top_level = (uu___110_14650.top_level);
        check_uvars = (uu___110_14650.check_uvars);
        use_eq = (uu___110_14650.use_eq);
        is_iface = (uu___110_14650.is_iface);
        admit = (uu___110_14650.admit);
        lax = (uu___110_14650.lax);
        lax_universes = (uu___110_14650.lax_universes);
        failhard = (uu___110_14650.failhard);
        nosynth = (uu___110_14650.nosynth);
        tc_term = (uu___110_14650.tc_term);
        type_of = (uu___110_14650.type_of);
        universe_of = (uu___110_14650.universe_of);
        check_type_of = (uu___110_14650.check_type_of);
        use_bv_sorts = (uu___110_14650.use_bv_sorts);
        qtbl_name_and_index = (uu___110_14650.qtbl_name_and_index);
        proof_ns = ns;
        synth = (uu___110_14650.synth);
        is_native_tactic = (uu___110_14650.is_native_tactic);
        identifier_info = (uu___110_14650.identifier_info);
        tc_hooks = (uu___110_14650.tc_hooks);
        dsenv = (uu___110_14650.dsenv);
        dep_graph = (uu___110_14650.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____14661 = FStar_Syntax_Free.names t  in
      let uu____14664 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14661 uu____14664
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____14681 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____14681
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14687 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____14687
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____14702 =
      match uu____14702 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14718 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____14718)
       in
    let uu____14720 =
      let uu____14723 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____14723 FStar_List.rev  in
    FStar_All.pipe_right uu____14720 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____14740  -> ());
    push = (fun uu____14742  -> ());
    pop = (fun uu____14744  -> ());
    encode_modul = (fun uu____14747  -> fun uu____14748  -> ());
    encode_sig = (fun uu____14751  -> fun uu____14752  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14758 =
             let uu____14765 = FStar_Options.peek ()  in (e, g, uu____14765)
              in
           [uu____14758]);
    solve = (fun uu____14781  -> fun uu____14782  -> fun uu____14783  -> ());
    finish = (fun uu____14789  -> ());
    refresh = (fun uu____14791  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___111_14795 = en  in
    let uu____14796 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____14799 = FStar_Util.smap_copy en.sigtab  in
    let uu____14802 = FStar_ToSyntax_Env.mk_copy en.dsenv  in
    {
      solver = (uu___111_14795.solver);
      range = (uu___111_14795.range);
      curmodule = (uu___111_14795.curmodule);
      gamma = (uu___111_14795.gamma);
      gamma_cache = uu____14796;
      modules = (uu___111_14795.modules);
      expected_typ = (uu___111_14795.expected_typ);
      sigtab = uu____14799;
      is_pattern = (uu___111_14795.is_pattern);
      instantiate_imp = (uu___111_14795.instantiate_imp);
      effects = (uu___111_14795.effects);
      generalize = (uu___111_14795.generalize);
      letrecs = (uu___111_14795.letrecs);
      top_level = (uu___111_14795.top_level);
      check_uvars = (uu___111_14795.check_uvars);
      use_eq = (uu___111_14795.use_eq);
      is_iface = (uu___111_14795.is_iface);
      admit = (uu___111_14795.admit);
      lax = (uu___111_14795.lax);
      lax_universes = (uu___111_14795.lax_universes);
      failhard = (uu___111_14795.failhard);
      nosynth = (uu___111_14795.nosynth);
      tc_term = (uu___111_14795.tc_term);
      type_of = (uu___111_14795.type_of);
      universe_of = (uu___111_14795.universe_of);
      check_type_of = (uu___111_14795.check_type_of);
      use_bv_sorts = (uu___111_14795.use_bv_sorts);
      qtbl_name_and_index = (uu___111_14795.qtbl_name_and_index);
      proof_ns = (uu___111_14795.proof_ns);
      synth = (uu___111_14795.synth);
      is_native_tactic = (uu___111_14795.is_native_tactic);
      identifier_info = (uu___111_14795.identifier_info);
      tc_hooks = (uu___111_14795.tc_hooks);
      dsenv = uu____14802;
      dep_graph = (uu___111_14795.dep_graph)
    }
  