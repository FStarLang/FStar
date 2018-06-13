open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | DoNotUnfoldPureLets 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe 
  | NBE 
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____35 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____41 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____47 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____54 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____67 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____73 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____79 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____85 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____91 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____97 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____104 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____120 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____142 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____162 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____175 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____181 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____187 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____193 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____199 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____205 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____211 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____217 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____223 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____229 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____235 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____241 -> false 
type steps = step Prims.list
type sig_binding =
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTacDelta 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____260 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____266 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____272 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____279 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
let (uu___is_UnfoldTacDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTacDelta  -> true | uu____292 -> false
  
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
    }
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
  mlift: mlift }
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
    }
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
  
type name_prefix = Prims.string Prims.list
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
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
  uvar_subtyping: Prims.bool ;
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
  dep_graph: FStar_Parser_Dep.deps ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    }
and solver_t =
  {
  init: env -> unit ;
  push: Prims.string -> unit ;
  pop: Prims.string -> unit ;
  snapshot:
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2
    ;
  rollback:
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit
    ;
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
  refresh: unit -> unit }
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
    (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
      FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list
    }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__sigtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__admit
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__lax
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__lax_universes
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__uvar_subtyping
  
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_term
  
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_bv_sorts
  
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
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__normalized_eff_names
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__synth_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__splice
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dsenv
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dep_graph
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__nbe
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t ->
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__snapshot
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__rollback
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
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
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
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
    (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
      FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type solver_depth_t =
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
type implicits =
  (Prims.string,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,
    FStar_Range.range) FStar_Pervasives_Native.tuple4 Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___218_9183  ->
              match uu___218_9183 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9186 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9186  in
                  let uu____9187 =
                    let uu____9188 = FStar_Syntax_Subst.compress y  in
                    uu____9188.FStar_Syntax_Syntax.n  in
                  (match uu____9187 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9192 =
                         let uu___232_9193 = y1  in
                         let uu____9194 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___232_9193.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___232_9193.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9194
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9192
                   | uu____9197 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___233_9209 = env  in
      let uu____9210 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___233_9209.solver);
        range = (uu___233_9209.range);
        curmodule = (uu___233_9209.curmodule);
        gamma = uu____9210;
        gamma_sig = (uu___233_9209.gamma_sig);
        gamma_cache = (uu___233_9209.gamma_cache);
        modules = (uu___233_9209.modules);
        expected_typ = (uu___233_9209.expected_typ);
        sigtab = (uu___233_9209.sigtab);
        is_pattern = (uu___233_9209.is_pattern);
        instantiate_imp = (uu___233_9209.instantiate_imp);
        effects = (uu___233_9209.effects);
        generalize = (uu___233_9209.generalize);
        letrecs = (uu___233_9209.letrecs);
        top_level = (uu___233_9209.top_level);
        check_uvars = (uu___233_9209.check_uvars);
        use_eq = (uu___233_9209.use_eq);
        is_iface = (uu___233_9209.is_iface);
        admit = (uu___233_9209.admit);
        lax = (uu___233_9209.lax);
        lax_universes = (uu___233_9209.lax_universes);
        failhard = (uu___233_9209.failhard);
        nosynth = (uu___233_9209.nosynth);
        uvar_subtyping = (uu___233_9209.uvar_subtyping);
        tc_term = (uu___233_9209.tc_term);
        type_of = (uu___233_9209.type_of);
        universe_of = (uu___233_9209.universe_of);
        check_type_of = (uu___233_9209.check_type_of);
        use_bv_sorts = (uu___233_9209.use_bv_sorts);
        qtbl_name_and_index = (uu___233_9209.qtbl_name_and_index);
        normalized_eff_names = (uu___233_9209.normalized_eff_names);
        proof_ns = (uu___233_9209.proof_ns);
        synth_hook = (uu___233_9209.synth_hook);
        splice = (uu___233_9209.splice);
        is_native_tactic = (uu___233_9209.is_native_tactic);
        identifier_info = (uu___233_9209.identifier_info);
        tc_hooks = (uu___233_9209.tc_hooks);
        dsenv = (uu___233_9209.dsenv);
        dep_graph = (uu___233_9209.dep_graph);
        nbe = (uu___233_9209.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9217  -> fun uu____9218  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___234_9238 = env  in
      {
        solver = (uu___234_9238.solver);
        range = (uu___234_9238.range);
        curmodule = (uu___234_9238.curmodule);
        gamma = (uu___234_9238.gamma);
        gamma_sig = (uu___234_9238.gamma_sig);
        gamma_cache = (uu___234_9238.gamma_cache);
        modules = (uu___234_9238.modules);
        expected_typ = (uu___234_9238.expected_typ);
        sigtab = (uu___234_9238.sigtab);
        is_pattern = (uu___234_9238.is_pattern);
        instantiate_imp = (uu___234_9238.instantiate_imp);
        effects = (uu___234_9238.effects);
        generalize = (uu___234_9238.generalize);
        letrecs = (uu___234_9238.letrecs);
        top_level = (uu___234_9238.top_level);
        check_uvars = (uu___234_9238.check_uvars);
        use_eq = (uu___234_9238.use_eq);
        is_iface = (uu___234_9238.is_iface);
        admit = (uu___234_9238.admit);
        lax = (uu___234_9238.lax);
        lax_universes = (uu___234_9238.lax_universes);
        failhard = (uu___234_9238.failhard);
        nosynth = (uu___234_9238.nosynth);
        uvar_subtyping = (uu___234_9238.uvar_subtyping);
        tc_term = (uu___234_9238.tc_term);
        type_of = (uu___234_9238.type_of);
        universe_of = (uu___234_9238.universe_of);
        check_type_of = (uu___234_9238.check_type_of);
        use_bv_sorts = (uu___234_9238.use_bv_sorts);
        qtbl_name_and_index = (uu___234_9238.qtbl_name_and_index);
        normalized_eff_names = (uu___234_9238.normalized_eff_names);
        proof_ns = (uu___234_9238.proof_ns);
        synth_hook = (uu___234_9238.synth_hook);
        splice = (uu___234_9238.splice);
        is_native_tactic = (uu___234_9238.is_native_tactic);
        identifier_info = (uu___234_9238.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___234_9238.dsenv);
        dep_graph = (uu___234_9238.dep_graph);
        nbe = (uu___234_9238.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___235_9249 = e  in
      {
        solver = (uu___235_9249.solver);
        range = (uu___235_9249.range);
        curmodule = (uu___235_9249.curmodule);
        gamma = (uu___235_9249.gamma);
        gamma_sig = (uu___235_9249.gamma_sig);
        gamma_cache = (uu___235_9249.gamma_cache);
        modules = (uu___235_9249.modules);
        expected_typ = (uu___235_9249.expected_typ);
        sigtab = (uu___235_9249.sigtab);
        is_pattern = (uu___235_9249.is_pattern);
        instantiate_imp = (uu___235_9249.instantiate_imp);
        effects = (uu___235_9249.effects);
        generalize = (uu___235_9249.generalize);
        letrecs = (uu___235_9249.letrecs);
        top_level = (uu___235_9249.top_level);
        check_uvars = (uu___235_9249.check_uvars);
        use_eq = (uu___235_9249.use_eq);
        is_iface = (uu___235_9249.is_iface);
        admit = (uu___235_9249.admit);
        lax = (uu___235_9249.lax);
        lax_universes = (uu___235_9249.lax_universes);
        failhard = (uu___235_9249.failhard);
        nosynth = (uu___235_9249.nosynth);
        uvar_subtyping = (uu___235_9249.uvar_subtyping);
        tc_term = (uu___235_9249.tc_term);
        type_of = (uu___235_9249.type_of);
        universe_of = (uu___235_9249.universe_of);
        check_type_of = (uu___235_9249.check_type_of);
        use_bv_sorts = (uu___235_9249.use_bv_sorts);
        qtbl_name_and_index = (uu___235_9249.qtbl_name_and_index);
        normalized_eff_names = (uu___235_9249.normalized_eff_names);
        proof_ns = (uu___235_9249.proof_ns);
        synth_hook = (uu___235_9249.synth_hook);
        splice = (uu___235_9249.splice);
        is_native_tactic = (uu___235_9249.is_native_tactic);
        identifier_info = (uu___235_9249.identifier_info);
        tc_hooks = (uu___235_9249.tc_hooks);
        dsenv = (uu___235_9249.dsenv);
        dep_graph = g;
        nbe = (uu___235_9249.nbe)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun e  -> e.dep_graph 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____9272) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____9273,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____9274,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____9275 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____9284 . unit -> 'Auu____9284 FStar_Util.smap =
  fun uu____9291  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____9296 . unit -> 'Auu____9296 FStar_Util.smap =
  fun uu____9303  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
            ->
            solver_t ->
              FStar_Ident.lident ->
                (step Prims.list ->
                   env ->
                     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
                  -> env)
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun check_type_of  ->
            fun solver  ->
              fun module_lid  ->
                fun nbe1  ->
                  let uu____9437 = new_gamma_cache ()  in
                  let uu____9440 = new_sigtab ()  in
                  let uu____9443 =
                    let uu____9456 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____9456, FStar_Pervasives_Native.None)  in
                  let uu____9471 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____9474 = FStar_Options.using_facts_from ()  in
                  let uu____9475 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____9478 = FStar_Syntax_DsEnv.empty_env ()  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____9437;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____9440;
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
                    uvar_subtyping = true;
                    tc_term;
                    type_of;
                    universe_of;
                    check_type_of;
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu____9443;
                    normalized_eff_names = uu____9471;
                    proof_ns = uu____9474;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____9514  -> false);
                    identifier_info = uu____9475;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____9478;
                    dep_graph = deps;
                    nbe = nbe1
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
let (push_query_indices : unit -> unit) =
  fun uu____9605  ->
    let uu____9606 = FStar_ST.op_Bang query_indices  in
    match uu____9606 with
    | [] -> failwith "Empty query indices!"
    | uu____9660 ->
        let uu____9669 =
          let uu____9678 =
            let uu____9685 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____9685  in
          let uu____9739 = FStar_ST.op_Bang query_indices  in uu____9678 ::
            uu____9739
           in
        FStar_ST.op_Colon_Equals query_indices uu____9669
  
let (pop_query_indices : unit -> unit) =
  fun uu____9836  ->
    let uu____9837 = FStar_ST.op_Bang query_indices  in
    match uu____9837 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____9960  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____9990  ->
    match uu____9990 with
    | (l,n1) ->
        let uu____9997 = FStar_ST.op_Bang query_indices  in
        (match uu____9997 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10116 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10135  ->
    let uu____10136 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10136
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10213 =
       let uu____10216 = FStar_ST.op_Bang stack  in env :: uu____10216  in
     FStar_ST.op_Colon_Equals stack uu____10213);
    (let uu___236_10273 = env  in
     let uu____10274 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____10277 = FStar_Util.smap_copy (sigtab env)  in
     let uu____10280 =
       let uu____10293 =
         let uu____10296 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____10296  in
       let uu____10321 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____10293, uu____10321)  in
     let uu____10362 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____10365 =
       let uu____10368 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____10368  in
     {
       solver = (uu___236_10273.solver);
       range = (uu___236_10273.range);
       curmodule = (uu___236_10273.curmodule);
       gamma = (uu___236_10273.gamma);
       gamma_sig = (uu___236_10273.gamma_sig);
       gamma_cache = uu____10274;
       modules = (uu___236_10273.modules);
       expected_typ = (uu___236_10273.expected_typ);
       sigtab = uu____10277;
       is_pattern = (uu___236_10273.is_pattern);
       instantiate_imp = (uu___236_10273.instantiate_imp);
       effects = (uu___236_10273.effects);
       generalize = (uu___236_10273.generalize);
       letrecs = (uu___236_10273.letrecs);
       top_level = (uu___236_10273.top_level);
       check_uvars = (uu___236_10273.check_uvars);
       use_eq = (uu___236_10273.use_eq);
       is_iface = (uu___236_10273.is_iface);
       admit = (uu___236_10273.admit);
       lax = (uu___236_10273.lax);
       lax_universes = (uu___236_10273.lax_universes);
       failhard = (uu___236_10273.failhard);
       nosynth = (uu___236_10273.nosynth);
       uvar_subtyping = (uu___236_10273.uvar_subtyping);
       tc_term = (uu___236_10273.tc_term);
       type_of = (uu___236_10273.type_of);
       universe_of = (uu___236_10273.universe_of);
       check_type_of = (uu___236_10273.check_type_of);
       use_bv_sorts = (uu___236_10273.use_bv_sorts);
       qtbl_name_and_index = uu____10280;
       normalized_eff_names = uu____10362;
       proof_ns = (uu___236_10273.proof_ns);
       synth_hook = (uu___236_10273.synth_hook);
       splice = (uu___236_10273.splice);
       is_native_tactic = (uu___236_10273.is_native_tactic);
       identifier_info = uu____10365;
       tc_hooks = (uu___236_10273.tc_hooks);
       dsenv = (uu___236_10273.dsenv);
       dep_graph = (uu___236_10273.dep_graph);
       nbe = (uu___236_10273.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____10418  ->
    let uu____10419 = FStar_ST.op_Bang stack  in
    match uu____10419 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10481 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2)
  = fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t =
  (Prims.int,Prims.int,solver_depth_t,Prims.int)
    FStar_Pervasives_Native.tuple4
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t,env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____10553  ->
           let uu____10554 = snapshot_stack env  in
           match uu____10554 with
           | (stack_depth,env1) ->
               let uu____10579 = snapshot_query_indices ()  in
               (match uu____10579 with
                | (query_indices_depth,()) ->
                    let uu____10603 = (env1.solver).snapshot msg  in
                    (match uu____10603 with
                     | (solver_depth,()) ->
                         let uu____10645 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____10645 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___237_10691 = env1  in
                                 {
                                   solver = (uu___237_10691.solver);
                                   range = (uu___237_10691.range);
                                   curmodule = (uu___237_10691.curmodule);
                                   gamma = (uu___237_10691.gamma);
                                   gamma_sig = (uu___237_10691.gamma_sig);
                                   gamma_cache = (uu___237_10691.gamma_cache);
                                   modules = (uu___237_10691.modules);
                                   expected_typ =
                                     (uu___237_10691.expected_typ);
                                   sigtab = (uu___237_10691.sigtab);
                                   is_pattern = (uu___237_10691.is_pattern);
                                   instantiate_imp =
                                     (uu___237_10691.instantiate_imp);
                                   effects = (uu___237_10691.effects);
                                   generalize = (uu___237_10691.generalize);
                                   letrecs = (uu___237_10691.letrecs);
                                   top_level = (uu___237_10691.top_level);
                                   check_uvars = (uu___237_10691.check_uvars);
                                   use_eq = (uu___237_10691.use_eq);
                                   is_iface = (uu___237_10691.is_iface);
                                   admit = (uu___237_10691.admit);
                                   lax = (uu___237_10691.lax);
                                   lax_universes =
                                     (uu___237_10691.lax_universes);
                                   failhard = (uu___237_10691.failhard);
                                   nosynth = (uu___237_10691.nosynth);
                                   uvar_subtyping =
                                     (uu___237_10691.uvar_subtyping);
                                   tc_term = (uu___237_10691.tc_term);
                                   type_of = (uu___237_10691.type_of);
                                   universe_of = (uu___237_10691.universe_of);
                                   check_type_of =
                                     (uu___237_10691.check_type_of);
                                   use_bv_sorts =
                                     (uu___237_10691.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___237_10691.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___237_10691.normalized_eff_names);
                                   proof_ns = (uu___237_10691.proof_ns);
                                   synth_hook = (uu___237_10691.synth_hook);
                                   splice = (uu___237_10691.splice);
                                   is_native_tactic =
                                     (uu___237_10691.is_native_tactic);
                                   identifier_info =
                                     (uu___237_10691.identifier_info);
                                   tc_hooks = (uu___237_10691.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___237_10691.dep_graph);
                                   nbe = (uu___237_10691.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____10722  ->
             let uu____10723 =
               match depth with
               | FStar_Pervasives_Native.Some (s1,s2,s3,s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None  ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None)
                in
             match uu____10723 with
             | (stack_depth,query_indices_depth,solver_depth,dsenv_depth) ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth  in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth  in
                             ((let uu____10849 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____10849
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____10860 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____10860
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____10887,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____10919 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____10945  ->
                  match uu____10945 with
                  | (m,uu____10951) -> FStar_Ident.lid_equals l m))
           in
        (match uu____10919 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___238_10959 = env  in
               {
                 solver = (uu___238_10959.solver);
                 range = (uu___238_10959.range);
                 curmodule = (uu___238_10959.curmodule);
                 gamma = (uu___238_10959.gamma);
                 gamma_sig = (uu___238_10959.gamma_sig);
                 gamma_cache = (uu___238_10959.gamma_cache);
                 modules = (uu___238_10959.modules);
                 expected_typ = (uu___238_10959.expected_typ);
                 sigtab = (uu___238_10959.sigtab);
                 is_pattern = (uu___238_10959.is_pattern);
                 instantiate_imp = (uu___238_10959.instantiate_imp);
                 effects = (uu___238_10959.effects);
                 generalize = (uu___238_10959.generalize);
                 letrecs = (uu___238_10959.letrecs);
                 top_level = (uu___238_10959.top_level);
                 check_uvars = (uu___238_10959.check_uvars);
                 use_eq = (uu___238_10959.use_eq);
                 is_iface = (uu___238_10959.is_iface);
                 admit = (uu___238_10959.admit);
                 lax = (uu___238_10959.lax);
                 lax_universes = (uu___238_10959.lax_universes);
                 failhard = (uu___238_10959.failhard);
                 nosynth = (uu___238_10959.nosynth);
                 uvar_subtyping = (uu___238_10959.uvar_subtyping);
                 tc_term = (uu___238_10959.tc_term);
                 type_of = (uu___238_10959.type_of);
                 universe_of = (uu___238_10959.universe_of);
                 check_type_of = (uu___238_10959.check_type_of);
                 use_bv_sorts = (uu___238_10959.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___238_10959.normalized_eff_names);
                 proof_ns = (uu___238_10959.proof_ns);
                 synth_hook = (uu___238_10959.synth_hook);
                 splice = (uu___238_10959.splice);
                 is_native_tactic = (uu___238_10959.is_native_tactic);
                 identifier_info = (uu___238_10959.identifier_info);
                 tc_hooks = (uu___238_10959.tc_hooks);
                 dsenv = (uu___238_10959.dsenv);
                 dep_graph = (uu___238_10959.dep_graph);
                 nbe = (uu___238_10959.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____10972,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___239_10981 = env  in
               {
                 solver = (uu___239_10981.solver);
                 range = (uu___239_10981.range);
                 curmodule = (uu___239_10981.curmodule);
                 gamma = (uu___239_10981.gamma);
                 gamma_sig = (uu___239_10981.gamma_sig);
                 gamma_cache = (uu___239_10981.gamma_cache);
                 modules = (uu___239_10981.modules);
                 expected_typ = (uu___239_10981.expected_typ);
                 sigtab = (uu___239_10981.sigtab);
                 is_pattern = (uu___239_10981.is_pattern);
                 instantiate_imp = (uu___239_10981.instantiate_imp);
                 effects = (uu___239_10981.effects);
                 generalize = (uu___239_10981.generalize);
                 letrecs = (uu___239_10981.letrecs);
                 top_level = (uu___239_10981.top_level);
                 check_uvars = (uu___239_10981.check_uvars);
                 use_eq = (uu___239_10981.use_eq);
                 is_iface = (uu___239_10981.is_iface);
                 admit = (uu___239_10981.admit);
                 lax = (uu___239_10981.lax);
                 lax_universes = (uu___239_10981.lax_universes);
                 failhard = (uu___239_10981.failhard);
                 nosynth = (uu___239_10981.nosynth);
                 uvar_subtyping = (uu___239_10981.uvar_subtyping);
                 tc_term = (uu___239_10981.tc_term);
                 type_of = (uu___239_10981.type_of);
                 universe_of = (uu___239_10981.universe_of);
                 check_type_of = (uu___239_10981.check_type_of);
                 use_bv_sorts = (uu___239_10981.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___239_10981.normalized_eff_names);
                 proof_ns = (uu___239_10981.proof_ns);
                 synth_hook = (uu___239_10981.synth_hook);
                 splice = (uu___239_10981.splice);
                 is_native_tactic = (uu___239_10981.is_native_tactic);
                 identifier_info = (uu___239_10981.identifier_info);
                 tc_hooks = (uu___239_10981.tc_hooks);
                 dsenv = (uu___239_10981.dsenv);
                 dep_graph = (uu___239_10981.dep_graph);
                 nbe = (uu___239_10981.nbe)
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
        (let uu___240_11015 = e  in
         {
           solver = (uu___240_11015.solver);
           range = r;
           curmodule = (uu___240_11015.curmodule);
           gamma = (uu___240_11015.gamma);
           gamma_sig = (uu___240_11015.gamma_sig);
           gamma_cache = (uu___240_11015.gamma_cache);
           modules = (uu___240_11015.modules);
           expected_typ = (uu___240_11015.expected_typ);
           sigtab = (uu___240_11015.sigtab);
           is_pattern = (uu___240_11015.is_pattern);
           instantiate_imp = (uu___240_11015.instantiate_imp);
           effects = (uu___240_11015.effects);
           generalize = (uu___240_11015.generalize);
           letrecs = (uu___240_11015.letrecs);
           top_level = (uu___240_11015.top_level);
           check_uvars = (uu___240_11015.check_uvars);
           use_eq = (uu___240_11015.use_eq);
           is_iface = (uu___240_11015.is_iface);
           admit = (uu___240_11015.admit);
           lax = (uu___240_11015.lax);
           lax_universes = (uu___240_11015.lax_universes);
           failhard = (uu___240_11015.failhard);
           nosynth = (uu___240_11015.nosynth);
           uvar_subtyping = (uu___240_11015.uvar_subtyping);
           tc_term = (uu___240_11015.tc_term);
           type_of = (uu___240_11015.type_of);
           universe_of = (uu___240_11015.universe_of);
           check_type_of = (uu___240_11015.check_type_of);
           use_bv_sorts = (uu___240_11015.use_bv_sorts);
           qtbl_name_and_index = (uu___240_11015.qtbl_name_and_index);
           normalized_eff_names = (uu___240_11015.normalized_eff_names);
           proof_ns = (uu___240_11015.proof_ns);
           synth_hook = (uu___240_11015.synth_hook);
           splice = (uu___240_11015.splice);
           is_native_tactic = (uu___240_11015.is_native_tactic);
           identifier_info = (uu___240_11015.identifier_info);
           tc_hooks = (uu___240_11015.tc_hooks);
           dsenv = (uu___240_11015.dsenv);
           dep_graph = (uu___240_11015.dep_graph);
           nbe = (uu___240_11015.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11031 =
        let uu____11032 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11032 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11031
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11094 =
          let uu____11095 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11095 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11094
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11157 =
          let uu____11158 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11158 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11157
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11220 =
        let uu____11221 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11221 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11220
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___241_11290 = env  in
      {
        solver = (uu___241_11290.solver);
        range = (uu___241_11290.range);
        curmodule = lid;
        gamma = (uu___241_11290.gamma);
        gamma_sig = (uu___241_11290.gamma_sig);
        gamma_cache = (uu___241_11290.gamma_cache);
        modules = (uu___241_11290.modules);
        expected_typ = (uu___241_11290.expected_typ);
        sigtab = (uu___241_11290.sigtab);
        is_pattern = (uu___241_11290.is_pattern);
        instantiate_imp = (uu___241_11290.instantiate_imp);
        effects = (uu___241_11290.effects);
        generalize = (uu___241_11290.generalize);
        letrecs = (uu___241_11290.letrecs);
        top_level = (uu___241_11290.top_level);
        check_uvars = (uu___241_11290.check_uvars);
        use_eq = (uu___241_11290.use_eq);
        is_iface = (uu___241_11290.is_iface);
        admit = (uu___241_11290.admit);
        lax = (uu___241_11290.lax);
        lax_universes = (uu___241_11290.lax_universes);
        failhard = (uu___241_11290.failhard);
        nosynth = (uu___241_11290.nosynth);
        uvar_subtyping = (uu___241_11290.uvar_subtyping);
        tc_term = (uu___241_11290.tc_term);
        type_of = (uu___241_11290.type_of);
        universe_of = (uu___241_11290.universe_of);
        check_type_of = (uu___241_11290.check_type_of);
        use_bv_sorts = (uu___241_11290.use_bv_sorts);
        qtbl_name_and_index = (uu___241_11290.qtbl_name_and_index);
        normalized_eff_names = (uu___241_11290.normalized_eff_names);
        proof_ns = (uu___241_11290.proof_ns);
        synth_hook = (uu___241_11290.synth_hook);
        splice = (uu___241_11290.splice);
        is_native_tactic = (uu___241_11290.is_native_tactic);
        identifier_info = (uu___241_11290.identifier_info);
        tc_hooks = (uu___241_11290.tc_hooks);
        dsenv = (uu___241_11290.dsenv);
        dep_graph = (uu___241_11290.dep_graph);
        nbe = (uu___241_11290.nbe)
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
      let uu____11317 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11317
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11327 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11327)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11337 =
      let uu____11338 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11338  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11337)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11343  ->
    let uu____11344 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11344
  
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
      | ((formals,t),uu____11400) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____11434 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11434)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___219_11450  ->
    match uu___219_11450 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11476  -> new_u_univ ()))
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
      let uu____11495 = inst_tscheme t  in
      match uu____11495 with
      | (us,t1) ->
          let uu____11506 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11506)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11526  ->
          match uu____11526 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11545 =
                         let uu____11546 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____11547 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____11548 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____11549 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11546 uu____11547 uu____11548 uu____11549
                          in
                       failwith uu____11545)
                    else ();
                    (let uu____11551 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____11551))
               | uu____11560 ->
                   let uu____11561 =
                     let uu____11562 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____11562
                      in
                   failwith uu____11561)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____11568 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11574 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11580 -> false
  
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
             | ([],uu____11622) -> Maybe
             | (uu____11629,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____11648 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
          let uu____11739 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____11739 with
          | FStar_Pervasives_Native.None  ->
              let uu____11762 =
                FStar_Util.find_map env.gamma
                  (fun uu___220_11806  ->
                     match uu___220_11806 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____11845 = FStar_Ident.lid_equals lid l  in
                         if uu____11845
                         then
                           let uu____11866 =
                             let uu____11885 =
                               let uu____11900 = inst_tscheme t  in
                               FStar_Util.Inl uu____11900  in
                             let uu____11915 = FStar_Ident.range_of_lid l  in
                             (uu____11885, uu____11915)  in
                           FStar_Pervasives_Native.Some uu____11866
                         else FStar_Pervasives_Native.None
                     | uu____11967 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____11762
                (fun uu____12005  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___221_12014  ->
                        match uu___221_12014 with
                        | (uu____12017,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12019);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12020;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12021;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12022;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12023;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12043 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12043
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids,s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____12091 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12098 -> cache t  in
                            let uu____12099 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12099 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12105 =
                                   let uu____12106 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12106)
                                    in
                                 maybe_cache uu____12105)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12174 = find_in_sigtab env lid  in
         match uu____12174 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12261) ->
          add_sigelts env ses
      | uu____12270 ->
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
            | uu____12284 -> ()))

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
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
        (fun uu___222_12315  ->
           match uu___222_12315 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12333 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____12394,lb::[]),uu____12396) ->
            let uu____12403 =
              let uu____12412 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____12421 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____12412, uu____12421)  in
            FStar_Pervasives_Native.Some uu____12403
        | FStar_Syntax_Syntax.Sig_let ((uu____12434,lbs),uu____12436) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____12466 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____12478 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____12478
                     then
                       let uu____12489 =
                         let uu____12498 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____12507 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____12498, uu____12507)  in
                       FStar_Pervasives_Native.Some uu____12489
                     else FStar_Pervasives_Native.None)
        | uu____12529 -> FStar_Pervasives_Native.None
  
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
          let uu____12588 =
            let uu____12597 =
              let uu____12602 =
                let uu____12603 =
                  let uu____12606 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____12606
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____12603)  in
              inst_tscheme1 uu____12602  in
            (uu____12597, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12588
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____12628,uu____12629) ->
          let uu____12634 =
            let uu____12643 =
              let uu____12648 =
                let uu____12649 =
                  let uu____12652 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____12652  in
                (us, uu____12649)  in
              inst_tscheme1 uu____12648  in
            (uu____12643, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____12634
      | uu____12671 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____12759 =
          match uu____12759 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____12855,uvs,t,uu____12858,uu____12859,uu____12860);
                      FStar_Syntax_Syntax.sigrng = uu____12861;
                      FStar_Syntax_Syntax.sigquals = uu____12862;
                      FStar_Syntax_Syntax.sigmeta = uu____12863;
                      FStar_Syntax_Syntax.sigattrs = uu____12864;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12885 =
                     let uu____12894 = inst_tscheme1 (uvs, t)  in
                     (uu____12894, rng)  in
                   FStar_Pervasives_Native.Some uu____12885
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____12918;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____12920;
                      FStar_Syntax_Syntax.sigattrs = uu____12921;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____12938 =
                     let uu____12939 = in_cur_mod env l  in uu____12939 = Yes
                      in
                   if uu____12938
                   then
                     let uu____12950 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____12950
                      then
                        let uu____12963 =
                          let uu____12972 = inst_tscheme1 (uvs, t)  in
                          (uu____12972, rng)  in
                        FStar_Pervasives_Native.Some uu____12963
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13003 =
                        let uu____13012 = inst_tscheme1 (uvs, t)  in
                        (uu____13012, rng)  in
                      FStar_Pervasives_Native.Some uu____13003)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13037,uu____13038);
                      FStar_Syntax_Syntax.sigrng = uu____13039;
                      FStar_Syntax_Syntax.sigquals = uu____13040;
                      FStar_Syntax_Syntax.sigmeta = uu____13041;
                      FStar_Syntax_Syntax.sigattrs = uu____13042;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13081 =
                          let uu____13090 = inst_tscheme1 (uvs, k)  in
                          (uu____13090, rng)  in
                        FStar_Pervasives_Native.Some uu____13081
                    | uu____13111 ->
                        let uu____13112 =
                          let uu____13121 =
                            let uu____13126 =
                              let uu____13127 =
                                let uu____13130 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13130
                                 in
                              (uvs, uu____13127)  in
                            inst_tscheme1 uu____13126  in
                          (uu____13121, rng)  in
                        FStar_Pervasives_Native.Some uu____13112)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13153,uu____13154);
                      FStar_Syntax_Syntax.sigrng = uu____13155;
                      FStar_Syntax_Syntax.sigquals = uu____13156;
                      FStar_Syntax_Syntax.sigmeta = uu____13157;
                      FStar_Syntax_Syntax.sigattrs = uu____13158;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13198 =
                          let uu____13207 = inst_tscheme_with (uvs, k) us  in
                          (uu____13207, rng)  in
                        FStar_Pervasives_Native.Some uu____13198
                    | uu____13228 ->
                        let uu____13229 =
                          let uu____13238 =
                            let uu____13243 =
                              let uu____13244 =
                                let uu____13247 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13247
                                 in
                              (uvs, uu____13244)  in
                            inst_tscheme_with uu____13243 us  in
                          (uu____13238, rng)  in
                        FStar_Pervasives_Native.Some uu____13229)
               | FStar_Util.Inr se ->
                   let uu____13283 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13304;
                          FStar_Syntax_Syntax.sigrng = uu____13305;
                          FStar_Syntax_Syntax.sigquals = uu____13306;
                          FStar_Syntax_Syntax.sigmeta = uu____13307;
                          FStar_Syntax_Syntax.sigattrs = uu____13308;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13323 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____13283
                     (FStar_Util.map_option
                        (fun uu____13371  ->
                           match uu____13371 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____13402 =
          let uu____13413 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____13413 mapper  in
        match uu____13402 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____13487 =
              let uu____13498 =
                let uu____13505 =
                  let uu___242_13508 = t  in
                  let uu____13509 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___242_13508.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____13509;
                    FStar_Syntax_Syntax.vars =
                      (uu___242_13508.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____13505)  in
              (uu____13498, r)  in
            FStar_Pervasives_Native.Some uu____13487
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13556 = lookup_qname env l  in
      match uu____13556 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____13575 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____13627 = try_lookup_bv env bv  in
      match uu____13627 with
      | FStar_Pervasives_Native.None  ->
          let uu____13642 = variable_not_found bv  in
          FStar_Errors.raise_error uu____13642 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____13657 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____13658 =
            let uu____13659 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____13659  in
          (uu____13657, uu____13658)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____13680 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____13680 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____13746 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____13746  in
          let uu____13747 =
            let uu____13756 =
              let uu____13761 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____13761)  in
            (uu____13756, r1)  in
          FStar_Pervasives_Native.Some uu____13747
  
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
        let uu____13795 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____13795 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____13828,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____13853 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____13853  in
            let uu____13854 =
              let uu____13859 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____13859, r1)  in
            FStar_Pervasives_Native.Some uu____13854
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____13882 = try_lookup_lid env l  in
      match uu____13882 with
      | FStar_Pervasives_Native.None  ->
          let uu____13909 = name_not_found l  in
          let uu____13914 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13909 uu____13914
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___223_13954  ->
              match uu___223_13954 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____13956 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13975 = lookup_qname env lid  in
      match uu____13975 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13984,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____13987;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13989;
              FStar_Syntax_Syntax.sigattrs = uu____13990;_},FStar_Pervasives_Native.None
            ),uu____13991)
          ->
          let uu____14040 =
            let uu____14047 =
              let uu____14048 =
                let uu____14051 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14051 t  in
              (uvs, uu____14048)  in
            (uu____14047, q)  in
          FStar_Pervasives_Native.Some uu____14040
      | uu____14064 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14085 = lookup_qname env lid  in
      match uu____14085 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14090,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14093;
              FStar_Syntax_Syntax.sigquals = uu____14094;
              FStar_Syntax_Syntax.sigmeta = uu____14095;
              FStar_Syntax_Syntax.sigattrs = uu____14096;_},FStar_Pervasives_Native.None
            ),uu____14097)
          ->
          let uu____14146 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14146 (uvs, t)
      | uu____14151 ->
          let uu____14152 = name_not_found lid  in
          let uu____14157 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14152 uu____14157
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14176 = lookup_qname env lid  in
      match uu____14176 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14181,uvs,t,uu____14184,uu____14185,uu____14186);
              FStar_Syntax_Syntax.sigrng = uu____14187;
              FStar_Syntax_Syntax.sigquals = uu____14188;
              FStar_Syntax_Syntax.sigmeta = uu____14189;
              FStar_Syntax_Syntax.sigattrs = uu____14190;_},FStar_Pervasives_Native.None
            ),uu____14191)
          ->
          let uu____14244 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14244 (uvs, t)
      | uu____14249 ->
          let uu____14250 = name_not_found lid  in
          let uu____14255 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14250 uu____14255
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14276 = lookup_qname env lid  in
      match uu____14276 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14283,uu____14284,uu____14285,uu____14286,uu____14287,dcs);
              FStar_Syntax_Syntax.sigrng = uu____14289;
              FStar_Syntax_Syntax.sigquals = uu____14290;
              FStar_Syntax_Syntax.sigmeta = uu____14291;
              FStar_Syntax_Syntax.sigattrs = uu____14292;_},uu____14293),uu____14294)
          -> (true, dcs)
      | uu____14355 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____14368 = lookup_qname env lid  in
      match uu____14368 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14369,uu____14370,uu____14371,l,uu____14373,uu____14374);
              FStar_Syntax_Syntax.sigrng = uu____14375;
              FStar_Syntax_Syntax.sigquals = uu____14376;
              FStar_Syntax_Syntax.sigmeta = uu____14377;
              FStar_Syntax_Syntax.sigattrs = uu____14378;_},uu____14379),uu____14380)
          -> l
      | uu____14435 ->
          let uu____14436 =
            let uu____14437 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____14437  in
          failwith uu____14436
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14486)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____14537,lbs),uu____14539)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____14561 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____14561
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____14593 -> FStar_Pervasives_Native.None)
        | uu____14598 -> FStar_Pervasives_Native.None
  
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
        let uu____14628 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____14628
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____14653),uu____14654) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____14703 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14724 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____14724
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____14743 = lookup_qname env ftv  in
      match uu____14743 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____14747) ->
          let uu____14792 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____14792 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____14813,t),r) ->
               let uu____14828 =
                 let uu____14829 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____14829 t  in
               FStar_Pervasives_Native.Some uu____14828)
      | uu____14830 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____14841 = try_lookup_effect_lid env ftv  in
      match uu____14841 with
      | FStar_Pervasives_Native.None  ->
          let uu____14844 = name_not_found ftv  in
          let uu____14849 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____14844 uu____14849
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
        let uu____14872 = lookup_qname env lid0  in
        match uu____14872 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____14883);
                FStar_Syntax_Syntax.sigrng = uu____14884;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____14886;
                FStar_Syntax_Syntax.sigattrs = uu____14887;_},FStar_Pervasives_Native.None
              ),uu____14888)
            ->
            let lid1 =
              let uu____14942 =
                let uu____14943 = FStar_Ident.range_of_lid lid  in
                let uu____14944 =
                  let uu____14945 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____14945  in
                FStar_Range.set_use_range uu____14943 uu____14944  in
              FStar_Ident.set_lid_range lid uu____14942  in
            let uu____14946 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___224_14950  ->
                      match uu___224_14950 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14951 -> false))
               in
            if uu____14946
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____14965 =
                      let uu____14966 =
                        let uu____14967 = get_range env  in
                        FStar_Range.string_of_range uu____14967  in
                      let uu____14968 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____14969 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____14966 uu____14968 uu____14969
                       in
                    failwith uu____14965)
                  in
               match (binders, univs1) with
               | ([],uu____14984) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____15005,uu____15006::uu____15007::uu____15008) ->
                   let uu____15025 =
                     let uu____15026 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____15027 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____15026 uu____15027
                      in
                   failwith uu____15025
               | uu____15034 ->
                   let uu____15047 =
                     let uu____15052 =
                       let uu____15053 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____15053)  in
                     inst_tscheme_with uu____15052 insts  in
                   (match uu____15047 with
                    | (uu____15066,t) ->
                        let t1 =
                          let uu____15069 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____15069 t  in
                        let uu____15070 =
                          let uu____15071 = FStar_Syntax_Subst.compress t1
                             in
                          uu____15071.FStar_Syntax_Syntax.n  in
                        (match uu____15070 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____15102 -> failwith "Impossible")))
        | uu____15109 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____15132 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____15132 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____15145,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____15152 = find1 l2  in
            (match uu____15152 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____15159 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____15159 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____15163 = find1 l  in
            (match uu____15163 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____15168 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____15168
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____15182 = lookup_qname env l1  in
      match uu____15182 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____15185;
              FStar_Syntax_Syntax.sigrng = uu____15186;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15188;
              FStar_Syntax_Syntax.sigattrs = uu____15189;_},uu____15190),uu____15191)
          -> q
      | uu____15242 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____15263 =
          let uu____15264 =
            let uu____15265 = FStar_Util.string_of_int i  in
            let uu____15266 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____15265 uu____15266
             in
          failwith uu____15264  in
        let uu____15267 = lookup_datacon env lid  in
        match uu____15267 with
        | (uu____15272,t) ->
            let uu____15274 =
              let uu____15275 = FStar_Syntax_Subst.compress t  in
              uu____15275.FStar_Syntax_Syntax.n  in
            (match uu____15274 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15279) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____15310 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____15310
                      FStar_Pervasives_Native.fst)
             | uu____15319 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15330 = lookup_qname env l  in
      match uu____15330 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15331,uu____15332,uu____15333);
              FStar_Syntax_Syntax.sigrng = uu____15334;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15336;
              FStar_Syntax_Syntax.sigattrs = uu____15337;_},uu____15338),uu____15339)
          ->
          FStar_Util.for_some
            (fun uu___225_15392  ->
               match uu___225_15392 with
               | FStar_Syntax_Syntax.Projector uu____15393 -> true
               | uu____15398 -> false) quals
      | uu____15399 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15410 = lookup_qname env lid  in
      match uu____15410 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15411,uu____15412,uu____15413,uu____15414,uu____15415,uu____15416);
              FStar_Syntax_Syntax.sigrng = uu____15417;
              FStar_Syntax_Syntax.sigquals = uu____15418;
              FStar_Syntax_Syntax.sigmeta = uu____15419;
              FStar_Syntax_Syntax.sigattrs = uu____15420;_},uu____15421),uu____15422)
          -> true
      | uu____15477 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15488 = lookup_qname env lid  in
      match uu____15488 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15489,uu____15490,uu____15491,uu____15492,uu____15493,uu____15494);
              FStar_Syntax_Syntax.sigrng = uu____15495;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____15497;
              FStar_Syntax_Syntax.sigattrs = uu____15498;_},uu____15499),uu____15500)
          ->
          FStar_Util.for_some
            (fun uu___226_15561  ->
               match uu___226_15561 with
               | FStar_Syntax_Syntax.RecordType uu____15562 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____15571 -> true
               | uu____15580 -> false) quals
      | uu____15581 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____15587,uu____15588);
            FStar_Syntax_Syntax.sigrng = uu____15589;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____15591;
            FStar_Syntax_Syntax.sigattrs = uu____15592;_},uu____15593),uu____15594)
        ->
        FStar_Util.for_some
          (fun uu___227_15651  ->
             match uu___227_15651 with
             | FStar_Syntax_Syntax.Action uu____15652 -> true
             | uu____15653 -> false) quals
    | uu____15654 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____15665 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____15665
  
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
      let uu____15679 =
        let uu____15680 = FStar_Syntax_Util.un_uinst head1  in
        uu____15680.FStar_Syntax_Syntax.n  in
      match uu____15679 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____15684 ->
               true
           | uu____15685 -> false)
      | uu____15686 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15697 = lookup_qname env l  in
      match uu____15697 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____15699),uu____15700) ->
          FStar_Util.for_some
            (fun uu___228_15748  ->
               match uu___228_15748 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____15749 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____15750 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____15821 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____15837) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____15854 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____15861 ->
                 FStar_Pervasives_Native.Some true
             | uu____15878 -> FStar_Pervasives_Native.Some false)
         in
      let uu____15879 =
        let uu____15882 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____15882 mapper  in
      match uu____15879 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____15932 = lookup_qname env lid  in
      match uu____15932 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15933,uu____15934,tps,uu____15936,uu____15937,uu____15938);
              FStar_Syntax_Syntax.sigrng = uu____15939;
              FStar_Syntax_Syntax.sigquals = uu____15940;
              FStar_Syntax_Syntax.sigmeta = uu____15941;
              FStar_Syntax_Syntax.sigattrs = uu____15942;_},uu____15943),uu____15944)
          -> FStar_List.length tps
      | uu____16007 ->
          let uu____16008 = name_not_found lid  in
          let uu____16013 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____16008 uu____16013
  
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
           (fun uu____16057  ->
              match uu____16057 with
              | (d,uu____16065) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____16080 = effect_decl_opt env l  in
      match uu____16080 with
      | FStar_Pervasives_Native.None  ->
          let uu____16095 = name_not_found l  in
          let uu____16100 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____16095 uu____16100
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____16122  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____16141  ->
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
        let uu____16172 = FStar_Ident.lid_equals l1 l2  in
        if uu____16172
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____16180 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____16180
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____16188 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____16241  ->
                        match uu____16241 with
                        | (m1,m2,uu____16254,uu____16255,uu____16256) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____16188 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16273 =
                    let uu____16278 =
                      let uu____16279 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____16280 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____16279
                        uu____16280
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____16278)
                     in
                  FStar_Errors.raise_error uu____16273 env.range
              | FStar_Pervasives_Native.Some
                  (uu____16287,uu____16288,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____16321 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____16321
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
  'Auu____16337 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____16337)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____16366 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____16392  ->
                match uu____16392 with
                | (d,uu____16398) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____16366 with
      | FStar_Pervasives_Native.None  ->
          let uu____16409 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____16409
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____16422 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____16422 with
           | (uu____16437,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____16453)::(wp,uu____16455)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____16491 -> failwith "Impossible"))
  
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
          let uu____16544 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____16544
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____16546 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____16546
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
                  let uu____16554 = get_range env  in
                  let uu____16555 =
                    let uu____16562 =
                      let uu____16563 =
                        let uu____16578 =
                          let uu____16587 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____16587]  in
                        (null_wp, uu____16578)  in
                      FStar_Syntax_Syntax.Tm_app uu____16563  in
                    FStar_Syntax_Syntax.mk uu____16562  in
                  uu____16555 FStar_Pervasives_Native.None uu____16554  in
                let uu____16619 =
                  let uu____16620 =
                    let uu____16629 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____16629]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____16620;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____16619))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___243_16660 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___243_16660.order);
              joins = (uu___243_16660.joins)
            }  in
          let uu___244_16669 = env  in
          {
            solver = (uu___244_16669.solver);
            range = (uu___244_16669.range);
            curmodule = (uu___244_16669.curmodule);
            gamma = (uu___244_16669.gamma);
            gamma_sig = (uu___244_16669.gamma_sig);
            gamma_cache = (uu___244_16669.gamma_cache);
            modules = (uu___244_16669.modules);
            expected_typ = (uu___244_16669.expected_typ);
            sigtab = (uu___244_16669.sigtab);
            is_pattern = (uu___244_16669.is_pattern);
            instantiate_imp = (uu___244_16669.instantiate_imp);
            effects;
            generalize = (uu___244_16669.generalize);
            letrecs = (uu___244_16669.letrecs);
            top_level = (uu___244_16669.top_level);
            check_uvars = (uu___244_16669.check_uvars);
            use_eq = (uu___244_16669.use_eq);
            is_iface = (uu___244_16669.is_iface);
            admit = (uu___244_16669.admit);
            lax = (uu___244_16669.lax);
            lax_universes = (uu___244_16669.lax_universes);
            failhard = (uu___244_16669.failhard);
            nosynth = (uu___244_16669.nosynth);
            uvar_subtyping = (uu___244_16669.uvar_subtyping);
            tc_term = (uu___244_16669.tc_term);
            type_of = (uu___244_16669.type_of);
            universe_of = (uu___244_16669.universe_of);
            check_type_of = (uu___244_16669.check_type_of);
            use_bv_sorts = (uu___244_16669.use_bv_sorts);
            qtbl_name_and_index = (uu___244_16669.qtbl_name_and_index);
            normalized_eff_names = (uu___244_16669.normalized_eff_names);
            proof_ns = (uu___244_16669.proof_ns);
            synth_hook = (uu___244_16669.synth_hook);
            splice = (uu___244_16669.splice);
            is_native_tactic = (uu___244_16669.is_native_tactic);
            identifier_info = (uu___244_16669.identifier_info);
            tc_hooks = (uu___244_16669.tc_hooks);
            dsenv = (uu___244_16669.dsenv);
            dep_graph = (uu___244_16669.dep_graph);
            nbe = (uu___244_16669.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____16699 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____16699  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____16857 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____16858 = l1 u t wp e  in
                                l2 u t uu____16857 uu____16858))
                | uu____16859 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____16931 = inst_tscheme_with lift_t [u]  in
            match uu____16931 with
            | (uu____16938,lift_t1) ->
                let uu____16940 =
                  let uu____16947 =
                    let uu____16948 =
                      let uu____16963 =
                        let uu____16972 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____16979 =
                          let uu____16988 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____16988]  in
                        uu____16972 :: uu____16979  in
                      (lift_t1, uu____16963)  in
                    FStar_Syntax_Syntax.Tm_app uu____16948  in
                  FStar_Syntax_Syntax.mk uu____16947  in
                uu____16940 FStar_Pervasives_Native.None
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
            let uu____17090 = inst_tscheme_with lift_t [u]  in
            match uu____17090 with
            | (uu____17097,lift_t1) ->
                let uu____17099 =
                  let uu____17106 =
                    let uu____17107 =
                      let uu____17122 =
                        let uu____17131 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17138 =
                          let uu____17147 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____17154 =
                            let uu____17163 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____17163]  in
                          uu____17147 :: uu____17154  in
                        uu____17131 :: uu____17138  in
                      (lift_t1, uu____17122)  in
                    FStar_Syntax_Syntax.Tm_app uu____17107  in
                  FStar_Syntax_Syntax.mk uu____17106  in
                uu____17099 FStar_Pervasives_Native.None
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
              let uu____17253 =
                let uu____17254 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____17254
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____17253  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____17258 =
              let uu____17259 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____17259  in
            let uu____17260 =
              let uu____17261 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____17287 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____17287)
                 in
              FStar_Util.dflt "none" uu____17261  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____17258
              uu____17260
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____17313  ->
                    match uu____17313 with
                    | (e,uu____17321) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____17344 =
            match uu____17344 with
            | (i,j) ->
                let uu____17355 = FStar_Ident.lid_equals i j  in
                if uu____17355
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____17387 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____17397 = FStar_Ident.lid_equals i k  in
                        if uu____17397
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____17408 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____17408
                                  then []
                                  else
                                    (let uu____17412 =
                                       let uu____17421 =
                                         find_edge order1 (i, k)  in
                                       let uu____17424 =
                                         find_edge order1 (k, j)  in
                                       (uu____17421, uu____17424)  in
                                     match uu____17412 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____17439 =
                                           compose_edges e1 e2  in
                                         [uu____17439]
                                     | uu____17440 -> [])))))
                 in
              FStar_List.append order1 uu____17387  in
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
                   let uu____17470 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____17472 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____17472
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____17470
                   then
                     let uu____17477 =
                       let uu____17482 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____17482)
                        in
                     let uu____17483 = get_range env  in
                     FStar_Errors.raise_error uu____17477 uu____17483
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____17560 = FStar_Ident.lid_equals i j
                                   in
                                if uu____17560
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____17609 =
                                              let uu____17618 =
                                                find_edge order2 (i, k)  in
                                              let uu____17621 =
                                                find_edge order2 (j, k)  in
                                              (uu____17618, uu____17621)  in
                                            match uu____17609 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____17663,uu____17664)
                                                     ->
                                                     let uu____17671 =
                                                       let uu____17676 =
                                                         let uu____17677 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17677
                                                          in
                                                       let uu____17680 =
                                                         let uu____17681 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____17681
                                                          in
                                                       (uu____17676,
                                                         uu____17680)
                                                        in
                                                     (match uu____17671 with
                                                      | (true ,true ) ->
                                                          let uu____17692 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____17692
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
                                            | uu____17717 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___245_17790 = env.effects  in
              { decls = (uu___245_17790.decls); order = order2; joins }  in
            let uu___246_17791 = env  in
            {
              solver = (uu___246_17791.solver);
              range = (uu___246_17791.range);
              curmodule = (uu___246_17791.curmodule);
              gamma = (uu___246_17791.gamma);
              gamma_sig = (uu___246_17791.gamma_sig);
              gamma_cache = (uu___246_17791.gamma_cache);
              modules = (uu___246_17791.modules);
              expected_typ = (uu___246_17791.expected_typ);
              sigtab = (uu___246_17791.sigtab);
              is_pattern = (uu___246_17791.is_pattern);
              instantiate_imp = (uu___246_17791.instantiate_imp);
              effects;
              generalize = (uu___246_17791.generalize);
              letrecs = (uu___246_17791.letrecs);
              top_level = (uu___246_17791.top_level);
              check_uvars = (uu___246_17791.check_uvars);
              use_eq = (uu___246_17791.use_eq);
              is_iface = (uu___246_17791.is_iface);
              admit = (uu___246_17791.admit);
              lax = (uu___246_17791.lax);
              lax_universes = (uu___246_17791.lax_universes);
              failhard = (uu___246_17791.failhard);
              nosynth = (uu___246_17791.nosynth);
              uvar_subtyping = (uu___246_17791.uvar_subtyping);
              tc_term = (uu___246_17791.tc_term);
              type_of = (uu___246_17791.type_of);
              universe_of = (uu___246_17791.universe_of);
              check_type_of = (uu___246_17791.check_type_of);
              use_bv_sorts = (uu___246_17791.use_bv_sorts);
              qtbl_name_and_index = (uu___246_17791.qtbl_name_and_index);
              normalized_eff_names = (uu___246_17791.normalized_eff_names);
              proof_ns = (uu___246_17791.proof_ns);
              synth_hook = (uu___246_17791.synth_hook);
              splice = (uu___246_17791.splice);
              is_native_tactic = (uu___246_17791.is_native_tactic);
              identifier_info = (uu___246_17791.identifier_info);
              tc_hooks = (uu___246_17791.tc_hooks);
              dsenv = (uu___246_17791.dsenv);
              dep_graph = (uu___246_17791.dep_graph);
              nbe = (uu___246_17791.nbe)
            }))
      | uu____17792 -> env
  
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
        | uu____17820 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____17832 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____17832 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____17849 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____17849 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____17867 =
                     let uu____17872 =
                       let uu____17873 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____17878 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____17885 =
                         let uu____17886 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____17886  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____17873 uu____17878 uu____17885
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____17872)
                      in
                   FStar_Errors.raise_error uu____17867
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____17891 =
                     let uu____17900 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____17900 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____17929  ->
                        fun uu____17930  ->
                          match (uu____17929, uu____17930) with
                          | ((x,uu____17952),(t,uu____17954)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____17891
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____17973 =
                     let uu___247_17974 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___247_17974.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___247_17974.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___247_17974.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___247_17974.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____17973
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
          let uu____18004 = effect_decl_opt env effect_name  in
          match uu____18004 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____18037 =
                only_reifiable &&
                  (let uu____18039 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____18039)
                 in
              if uu____18037
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____18055 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____18074 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____18103 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____18103
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____18104 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____18104
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____18116 =
                       let uu____18119 = get_range env  in
                       let uu____18120 =
                         let uu____18127 =
                           let uu____18128 =
                             let uu____18143 =
                               let uu____18152 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____18152; wp]  in
                             (repr, uu____18143)  in
                           FStar_Syntax_Syntax.Tm_app uu____18128  in
                         FStar_Syntax_Syntax.mk uu____18127  in
                       uu____18120 FStar_Pervasives_Native.None uu____18119
                        in
                     FStar_Pervasives_Native.Some uu____18116)
  
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
          let uu____18232 =
            let uu____18237 =
              let uu____18238 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____18238
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____18237)  in
          let uu____18239 = get_range env  in
          FStar_Errors.raise_error uu____18232 uu____18239  in
        let uu____18240 = effect_repr_aux true env c u_c  in
        match uu____18240 with
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
      | uu____18286 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____18297 =
        let uu____18298 = FStar_Syntax_Subst.compress t  in
        uu____18298.FStar_Syntax_Syntax.n  in
      match uu____18297 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____18301,c) ->
          is_reifiable_comp env c
      | uu____18319 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___248_18340 = env  in
        {
          solver = (uu___248_18340.solver);
          range = (uu___248_18340.range);
          curmodule = (uu___248_18340.curmodule);
          gamma = (uu___248_18340.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___248_18340.gamma_cache);
          modules = (uu___248_18340.modules);
          expected_typ = (uu___248_18340.expected_typ);
          sigtab = (uu___248_18340.sigtab);
          is_pattern = (uu___248_18340.is_pattern);
          instantiate_imp = (uu___248_18340.instantiate_imp);
          effects = (uu___248_18340.effects);
          generalize = (uu___248_18340.generalize);
          letrecs = (uu___248_18340.letrecs);
          top_level = (uu___248_18340.top_level);
          check_uvars = (uu___248_18340.check_uvars);
          use_eq = (uu___248_18340.use_eq);
          is_iface = (uu___248_18340.is_iface);
          admit = (uu___248_18340.admit);
          lax = (uu___248_18340.lax);
          lax_universes = (uu___248_18340.lax_universes);
          failhard = (uu___248_18340.failhard);
          nosynth = (uu___248_18340.nosynth);
          uvar_subtyping = (uu___248_18340.uvar_subtyping);
          tc_term = (uu___248_18340.tc_term);
          type_of = (uu___248_18340.type_of);
          universe_of = (uu___248_18340.universe_of);
          check_type_of = (uu___248_18340.check_type_of);
          use_bv_sorts = (uu___248_18340.use_bv_sorts);
          qtbl_name_and_index = (uu___248_18340.qtbl_name_and_index);
          normalized_eff_names = (uu___248_18340.normalized_eff_names);
          proof_ns = (uu___248_18340.proof_ns);
          synth_hook = (uu___248_18340.synth_hook);
          splice = (uu___248_18340.splice);
          is_native_tactic = (uu___248_18340.is_native_tactic);
          identifier_info = (uu___248_18340.identifier_info);
          tc_hooks = (uu___248_18340.tc_hooks);
          dsenv = (uu___248_18340.dsenv);
          dep_graph = (uu___248_18340.dep_graph);
          nbe = (uu___248_18340.nbe)
        }  in
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___249_18352 = env  in
      {
        solver = (uu___249_18352.solver);
        range = (uu___249_18352.range);
        curmodule = (uu___249_18352.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___249_18352.gamma_sig);
        gamma_cache = (uu___249_18352.gamma_cache);
        modules = (uu___249_18352.modules);
        expected_typ = (uu___249_18352.expected_typ);
        sigtab = (uu___249_18352.sigtab);
        is_pattern = (uu___249_18352.is_pattern);
        instantiate_imp = (uu___249_18352.instantiate_imp);
        effects = (uu___249_18352.effects);
        generalize = (uu___249_18352.generalize);
        letrecs = (uu___249_18352.letrecs);
        top_level = (uu___249_18352.top_level);
        check_uvars = (uu___249_18352.check_uvars);
        use_eq = (uu___249_18352.use_eq);
        is_iface = (uu___249_18352.is_iface);
        admit = (uu___249_18352.admit);
        lax = (uu___249_18352.lax);
        lax_universes = (uu___249_18352.lax_universes);
        failhard = (uu___249_18352.failhard);
        nosynth = (uu___249_18352.nosynth);
        uvar_subtyping = (uu___249_18352.uvar_subtyping);
        tc_term = (uu___249_18352.tc_term);
        type_of = (uu___249_18352.type_of);
        universe_of = (uu___249_18352.universe_of);
        check_type_of = (uu___249_18352.check_type_of);
        use_bv_sorts = (uu___249_18352.use_bv_sorts);
        qtbl_name_and_index = (uu___249_18352.qtbl_name_and_index);
        normalized_eff_names = (uu___249_18352.normalized_eff_names);
        proof_ns = (uu___249_18352.proof_ns);
        synth_hook = (uu___249_18352.synth_hook);
        splice = (uu___249_18352.splice);
        is_native_tactic = (uu___249_18352.is_native_tactic);
        identifier_info = (uu___249_18352.identifier_info);
        tc_hooks = (uu___249_18352.tc_hooks);
        dsenv = (uu___249_18352.dsenv);
        dep_graph = (uu___249_18352.dep_graph);
        nbe = (uu___249_18352.nbe)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___250_18407 = env  in
             {
               solver = (uu___250_18407.solver);
               range = (uu___250_18407.range);
               curmodule = (uu___250_18407.curmodule);
               gamma = rest;
               gamma_sig = (uu___250_18407.gamma_sig);
               gamma_cache = (uu___250_18407.gamma_cache);
               modules = (uu___250_18407.modules);
               expected_typ = (uu___250_18407.expected_typ);
               sigtab = (uu___250_18407.sigtab);
               is_pattern = (uu___250_18407.is_pattern);
               instantiate_imp = (uu___250_18407.instantiate_imp);
               effects = (uu___250_18407.effects);
               generalize = (uu___250_18407.generalize);
               letrecs = (uu___250_18407.letrecs);
               top_level = (uu___250_18407.top_level);
               check_uvars = (uu___250_18407.check_uvars);
               use_eq = (uu___250_18407.use_eq);
               is_iface = (uu___250_18407.is_iface);
               admit = (uu___250_18407.admit);
               lax = (uu___250_18407.lax);
               lax_universes = (uu___250_18407.lax_universes);
               failhard = (uu___250_18407.failhard);
               nosynth = (uu___250_18407.nosynth);
               uvar_subtyping = (uu___250_18407.uvar_subtyping);
               tc_term = (uu___250_18407.tc_term);
               type_of = (uu___250_18407.type_of);
               universe_of = (uu___250_18407.universe_of);
               check_type_of = (uu___250_18407.check_type_of);
               use_bv_sorts = (uu___250_18407.use_bv_sorts);
               qtbl_name_and_index = (uu___250_18407.qtbl_name_and_index);
               normalized_eff_names = (uu___250_18407.normalized_eff_names);
               proof_ns = (uu___250_18407.proof_ns);
               synth_hook = (uu___250_18407.synth_hook);
               splice = (uu___250_18407.splice);
               is_native_tactic = (uu___250_18407.is_native_tactic);
               identifier_info = (uu___250_18407.identifier_info);
               tc_hooks = (uu___250_18407.tc_hooks);
               dsenv = (uu___250_18407.dsenv);
               dep_graph = (uu___250_18407.dep_graph);
               nbe = (uu___250_18407.nbe)
             }))
    | uu____18408 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____18434  ->
             match uu____18434 with | (x,uu____18440) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___251_18470 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___251_18470.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___251_18470.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___252_18510 = env  in
       {
         solver = (uu___252_18510.solver);
         range = (uu___252_18510.range);
         curmodule = (uu___252_18510.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___252_18510.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___252_18510.sigtab);
         is_pattern = (uu___252_18510.is_pattern);
         instantiate_imp = (uu___252_18510.instantiate_imp);
         effects = (uu___252_18510.effects);
         generalize = (uu___252_18510.generalize);
         letrecs = (uu___252_18510.letrecs);
         top_level = (uu___252_18510.top_level);
         check_uvars = (uu___252_18510.check_uvars);
         use_eq = (uu___252_18510.use_eq);
         is_iface = (uu___252_18510.is_iface);
         admit = (uu___252_18510.admit);
         lax = (uu___252_18510.lax);
         lax_universes = (uu___252_18510.lax_universes);
         failhard = (uu___252_18510.failhard);
         nosynth = (uu___252_18510.nosynth);
         uvar_subtyping = (uu___252_18510.uvar_subtyping);
         tc_term = (uu___252_18510.tc_term);
         type_of = (uu___252_18510.type_of);
         universe_of = (uu___252_18510.universe_of);
         check_type_of = (uu___252_18510.check_type_of);
         use_bv_sorts = (uu___252_18510.use_bv_sorts);
         qtbl_name_and_index = (uu___252_18510.qtbl_name_and_index);
         normalized_eff_names = (uu___252_18510.normalized_eff_names);
         proof_ns = (uu___252_18510.proof_ns);
         synth_hook = (uu___252_18510.synth_hook);
         splice = (uu___252_18510.splice);
         is_native_tactic = (uu___252_18510.is_native_tactic);
         identifier_info = (uu___252_18510.identifier_info);
         tc_hooks = (uu___252_18510.tc_hooks);
         dsenv = (uu___252_18510.dsenv);
         dep_graph = (uu___252_18510.dep_graph);
         nbe = (uu___252_18510.nbe)
       })
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
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
        let uu____18552 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____18552 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____18580 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____18580)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___253_18595 = env  in
      {
        solver = (uu___253_18595.solver);
        range = (uu___253_18595.range);
        curmodule = (uu___253_18595.curmodule);
        gamma = (uu___253_18595.gamma);
        gamma_sig = (uu___253_18595.gamma_sig);
        gamma_cache = (uu___253_18595.gamma_cache);
        modules = (uu___253_18595.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___253_18595.sigtab);
        is_pattern = (uu___253_18595.is_pattern);
        instantiate_imp = (uu___253_18595.instantiate_imp);
        effects = (uu___253_18595.effects);
        generalize = (uu___253_18595.generalize);
        letrecs = (uu___253_18595.letrecs);
        top_level = (uu___253_18595.top_level);
        check_uvars = (uu___253_18595.check_uvars);
        use_eq = false;
        is_iface = (uu___253_18595.is_iface);
        admit = (uu___253_18595.admit);
        lax = (uu___253_18595.lax);
        lax_universes = (uu___253_18595.lax_universes);
        failhard = (uu___253_18595.failhard);
        nosynth = (uu___253_18595.nosynth);
        uvar_subtyping = (uu___253_18595.uvar_subtyping);
        tc_term = (uu___253_18595.tc_term);
        type_of = (uu___253_18595.type_of);
        universe_of = (uu___253_18595.universe_of);
        check_type_of = (uu___253_18595.check_type_of);
        use_bv_sorts = (uu___253_18595.use_bv_sorts);
        qtbl_name_and_index = (uu___253_18595.qtbl_name_and_index);
        normalized_eff_names = (uu___253_18595.normalized_eff_names);
        proof_ns = (uu___253_18595.proof_ns);
        synth_hook = (uu___253_18595.synth_hook);
        splice = (uu___253_18595.splice);
        is_native_tactic = (uu___253_18595.is_native_tactic);
        identifier_info = (uu___253_18595.identifier_info);
        tc_hooks = (uu___253_18595.tc_hooks);
        dsenv = (uu___253_18595.dsenv);
        dep_graph = (uu___253_18595.dep_graph);
        nbe = (uu___253_18595.nbe)
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
    let uu____18623 = expected_typ env_  in
    ((let uu___254_18629 = env_  in
      {
        solver = (uu___254_18629.solver);
        range = (uu___254_18629.range);
        curmodule = (uu___254_18629.curmodule);
        gamma = (uu___254_18629.gamma);
        gamma_sig = (uu___254_18629.gamma_sig);
        gamma_cache = (uu___254_18629.gamma_cache);
        modules = (uu___254_18629.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___254_18629.sigtab);
        is_pattern = (uu___254_18629.is_pattern);
        instantiate_imp = (uu___254_18629.instantiate_imp);
        effects = (uu___254_18629.effects);
        generalize = (uu___254_18629.generalize);
        letrecs = (uu___254_18629.letrecs);
        top_level = (uu___254_18629.top_level);
        check_uvars = (uu___254_18629.check_uvars);
        use_eq = false;
        is_iface = (uu___254_18629.is_iface);
        admit = (uu___254_18629.admit);
        lax = (uu___254_18629.lax);
        lax_universes = (uu___254_18629.lax_universes);
        failhard = (uu___254_18629.failhard);
        nosynth = (uu___254_18629.nosynth);
        uvar_subtyping = (uu___254_18629.uvar_subtyping);
        tc_term = (uu___254_18629.tc_term);
        type_of = (uu___254_18629.type_of);
        universe_of = (uu___254_18629.universe_of);
        check_type_of = (uu___254_18629.check_type_of);
        use_bv_sorts = (uu___254_18629.use_bv_sorts);
        qtbl_name_and_index = (uu___254_18629.qtbl_name_and_index);
        normalized_eff_names = (uu___254_18629.normalized_eff_names);
        proof_ns = (uu___254_18629.proof_ns);
        synth_hook = (uu___254_18629.synth_hook);
        splice = (uu___254_18629.splice);
        is_native_tactic = (uu___254_18629.is_native_tactic);
        identifier_info = (uu___254_18629.identifier_info);
        tc_hooks = (uu___254_18629.tc_hooks);
        dsenv = (uu___254_18629.dsenv);
        dep_graph = (uu___254_18629.dep_graph);
        nbe = (uu___254_18629.nbe)
      }), uu____18623)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____18639 =
      let uu____18642 = FStar_Ident.id_of_text ""  in [uu____18642]  in
    FStar_Ident.lid_of_ids uu____18639  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____18648 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____18648
        then
          let uu____18651 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____18651 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___255_18678 = env  in
       {
         solver = (uu___255_18678.solver);
         range = (uu___255_18678.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___255_18678.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___255_18678.expected_typ);
         sigtab = (uu___255_18678.sigtab);
         is_pattern = (uu___255_18678.is_pattern);
         instantiate_imp = (uu___255_18678.instantiate_imp);
         effects = (uu___255_18678.effects);
         generalize = (uu___255_18678.generalize);
         letrecs = (uu___255_18678.letrecs);
         top_level = (uu___255_18678.top_level);
         check_uvars = (uu___255_18678.check_uvars);
         use_eq = (uu___255_18678.use_eq);
         is_iface = (uu___255_18678.is_iface);
         admit = (uu___255_18678.admit);
         lax = (uu___255_18678.lax);
         lax_universes = (uu___255_18678.lax_universes);
         failhard = (uu___255_18678.failhard);
         nosynth = (uu___255_18678.nosynth);
         uvar_subtyping = (uu___255_18678.uvar_subtyping);
         tc_term = (uu___255_18678.tc_term);
         type_of = (uu___255_18678.type_of);
         universe_of = (uu___255_18678.universe_of);
         check_type_of = (uu___255_18678.check_type_of);
         use_bv_sorts = (uu___255_18678.use_bv_sorts);
         qtbl_name_and_index = (uu___255_18678.qtbl_name_and_index);
         normalized_eff_names = (uu___255_18678.normalized_eff_names);
         proof_ns = (uu___255_18678.proof_ns);
         synth_hook = (uu___255_18678.synth_hook);
         splice = (uu___255_18678.splice);
         is_native_tactic = (uu___255_18678.is_native_tactic);
         identifier_info = (uu___255_18678.identifier_info);
         tc_hooks = (uu___255_18678.tc_hooks);
         dsenv = (uu___255_18678.dsenv);
         dep_graph = (uu___255_18678.dep_graph);
         nbe = (uu___255_18678.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18729)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18733,(uu____18734,t)))::tl1
          ->
          let uu____18755 =
            let uu____18758 = FStar_Syntax_Free.uvars t  in
            ext out uu____18758  in
          aux uu____18755 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18761;
            FStar_Syntax_Syntax.index = uu____18762;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18769 =
            let uu____18772 = FStar_Syntax_Free.uvars t  in
            ext out uu____18772  in
          aux uu____18769 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____18829)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18833,(uu____18834,t)))::tl1
          ->
          let uu____18855 =
            let uu____18858 = FStar_Syntax_Free.univs t  in
            ext out uu____18858  in
          aux uu____18855 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18861;
            FStar_Syntax_Syntax.index = uu____18862;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18869 =
            let uu____18872 = FStar_Syntax_Free.univs t  in
            ext out uu____18872  in
          aux uu____18869 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____18933 = FStar_Util.set_add uname out  in
          aux uu____18933 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____18936,(uu____18937,t)))::tl1
          ->
          let uu____18958 =
            let uu____18961 = FStar_Syntax_Free.univnames t  in
            ext out uu____18961  in
          aux uu____18958 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____18964;
            FStar_Syntax_Syntax.index = uu____18965;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____18972 =
            let uu____18975 = FStar_Syntax_Free.univnames t  in
            ext out uu____18975  in
          aux uu____18972 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___229_18995  ->
            match uu___229_18995 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____18999 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____19012 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____19022 =
      let uu____19029 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____19029
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____19022 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____19067 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___230_19077  ->
              match uu___230_19077 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____19079 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____19079
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____19082) ->
                  let uu____19099 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____19099))
       in
    FStar_All.pipe_right uu____19067 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___231_19106  ->
    match uu___231_19106 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____19108 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____19108
    | UnfoldTacDelta  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____19128  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____19170) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____19189,uu____19190) -> false  in
      let uu____19199 =
        FStar_List.tryFind
          (fun uu____19217  ->
             match uu____19217 with | (p,uu____19225) -> list_prefix p path)
          env.proof_ns
         in
      match uu____19199 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____19236,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19258 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____19258
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___256_19276 = e  in
        {
          solver = (uu___256_19276.solver);
          range = (uu___256_19276.range);
          curmodule = (uu___256_19276.curmodule);
          gamma = (uu___256_19276.gamma);
          gamma_sig = (uu___256_19276.gamma_sig);
          gamma_cache = (uu___256_19276.gamma_cache);
          modules = (uu___256_19276.modules);
          expected_typ = (uu___256_19276.expected_typ);
          sigtab = (uu___256_19276.sigtab);
          is_pattern = (uu___256_19276.is_pattern);
          instantiate_imp = (uu___256_19276.instantiate_imp);
          effects = (uu___256_19276.effects);
          generalize = (uu___256_19276.generalize);
          letrecs = (uu___256_19276.letrecs);
          top_level = (uu___256_19276.top_level);
          check_uvars = (uu___256_19276.check_uvars);
          use_eq = (uu___256_19276.use_eq);
          is_iface = (uu___256_19276.is_iface);
          admit = (uu___256_19276.admit);
          lax = (uu___256_19276.lax);
          lax_universes = (uu___256_19276.lax_universes);
          failhard = (uu___256_19276.failhard);
          nosynth = (uu___256_19276.nosynth);
          uvar_subtyping = (uu___256_19276.uvar_subtyping);
          tc_term = (uu___256_19276.tc_term);
          type_of = (uu___256_19276.type_of);
          universe_of = (uu___256_19276.universe_of);
          check_type_of = (uu___256_19276.check_type_of);
          use_bv_sorts = (uu___256_19276.use_bv_sorts);
          qtbl_name_and_index = (uu___256_19276.qtbl_name_and_index);
          normalized_eff_names = (uu___256_19276.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___256_19276.synth_hook);
          splice = (uu___256_19276.splice);
          is_native_tactic = (uu___256_19276.is_native_tactic);
          identifier_info = (uu___256_19276.identifier_info);
          tc_hooks = (uu___256_19276.tc_hooks);
          dsenv = (uu___256_19276.dsenv);
          dep_graph = (uu___256_19276.dep_graph);
          nbe = (uu___256_19276.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___257_19316 = e  in
      {
        solver = (uu___257_19316.solver);
        range = (uu___257_19316.range);
        curmodule = (uu___257_19316.curmodule);
        gamma = (uu___257_19316.gamma);
        gamma_sig = (uu___257_19316.gamma_sig);
        gamma_cache = (uu___257_19316.gamma_cache);
        modules = (uu___257_19316.modules);
        expected_typ = (uu___257_19316.expected_typ);
        sigtab = (uu___257_19316.sigtab);
        is_pattern = (uu___257_19316.is_pattern);
        instantiate_imp = (uu___257_19316.instantiate_imp);
        effects = (uu___257_19316.effects);
        generalize = (uu___257_19316.generalize);
        letrecs = (uu___257_19316.letrecs);
        top_level = (uu___257_19316.top_level);
        check_uvars = (uu___257_19316.check_uvars);
        use_eq = (uu___257_19316.use_eq);
        is_iface = (uu___257_19316.is_iface);
        admit = (uu___257_19316.admit);
        lax = (uu___257_19316.lax);
        lax_universes = (uu___257_19316.lax_universes);
        failhard = (uu___257_19316.failhard);
        nosynth = (uu___257_19316.nosynth);
        uvar_subtyping = (uu___257_19316.uvar_subtyping);
        tc_term = (uu___257_19316.tc_term);
        type_of = (uu___257_19316.type_of);
        universe_of = (uu___257_19316.universe_of);
        check_type_of = (uu___257_19316.check_type_of);
        use_bv_sorts = (uu___257_19316.use_bv_sorts);
        qtbl_name_and_index = (uu___257_19316.qtbl_name_and_index);
        normalized_eff_names = (uu___257_19316.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___257_19316.synth_hook);
        splice = (uu___257_19316.splice);
        is_native_tactic = (uu___257_19316.is_native_tactic);
        identifier_info = (uu___257_19316.identifier_info);
        tc_hooks = (uu___257_19316.tc_hooks);
        dsenv = (uu___257_19316.dsenv);
        dep_graph = (uu___257_19316.dep_graph);
        nbe = (uu___257_19316.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____19331 = FStar_Syntax_Free.names t  in
      let uu____19334 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____19331 uu____19334
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____19355 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____19355
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____19363 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____19363
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____19380 =
      match uu____19380 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____19390 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____19390)
       in
    let uu____19392 =
      let uu____19395 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____19395 FStar_List.rev  in
    FStar_All.pipe_right uu____19392 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = [];
        univ_ineqs = ([],[]); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun uu____19481  ->
                match uu____19481 with
                | (uu____19490,uu____19491,ctx_uvar,uu____19493) ->
                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check =
                       FStar_Syntax_Syntax.Allow_unresolved)
                      ||
                      (let uu____19496 =
                         FStar_Syntax_Unionfind.find
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       (match uu____19496 with
                        | FStar_Pervasives_Native.Some uu____19499 -> true
                        | FStar_Pervasives_Native.None  -> false))))
    | uu____19500 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____19506;
        univ_ineqs = uu____19507; implicits = uu____19508;_} -> true
    | uu____19527 -> false
  
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___258_19562 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___258_19562.deferred);
            univ_ineqs = (uu___258_19562.univ_ineqs);
            implicits = (uu___258_19562.implicits)
          }
  
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____19597 = FStar_Options.defensive ()  in
          if uu____19597
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____19601 =
              let uu____19602 =
                let uu____19603 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____19603  in
              Prims.op_Negation uu____19602  in
            (if uu____19601
             then
               let uu____19608 =
                 let uu____19613 =
                   let uu____19614 = FStar_Syntax_Print.term_to_string t  in
                   let uu____19615 =
                     let uu____19616 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____19616
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____19614 uu____19615
                    in
                 (FStar_Errors.Warning_Defensive, uu____19613)  in
               FStar_Errors.log_issue rng uu____19608
             else ())
          else ()
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____19647 =
            let uu____19648 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19648  in
          if uu____19647
          then ()
          else
            (let uu____19650 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____19650 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____19673 =
            let uu____19674 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____19674  in
          if uu____19673
          then ()
          else
            (let uu____19676 = bound_vars e  in
             def_check_closed_in rng msg uu____19676 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___259_19711 = g  in
          let uu____19712 =
            let uu____19713 =
              let uu____19714 =
                let uu____19721 =
                  let uu____19722 =
                    let uu____19737 =
                      let uu____19746 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____19746]  in
                    (f, uu____19737)  in
                  FStar_Syntax_Syntax.Tm_app uu____19722  in
                FStar_Syntax_Syntax.mk uu____19721  in
              uu____19714 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____19713
             in
          {
            guard_f = uu____19712;
            deferred = (uu___259_19711.deferred);
            univ_ineqs = (uu___259_19711.univ_ineqs);
            implicits = (uu___259_19711.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___260_19794 = g  in
          let uu____19795 =
            let uu____19796 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____19796  in
          {
            guard_f = uu____19795;
            deferred = (uu___260_19794.deferred);
            univ_ineqs = (uu___260_19794.univ_ineqs);
            implicits = (uu___260_19794.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____19802 ->
        failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____19817 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____19817
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____19823 =
      let uu____19824 = FStar_Syntax_Util.unmeta t  in
      uu____19824.FStar_Syntax_Syntax.n  in
    match uu____19823 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____19828 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____19869 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____19869;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____19954 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____19954
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___261_19956 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___261_19956.deferred);
              univ_ineqs = (uu___261_19956.univ_ineqs);
              implicits = (uu___261_19956.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____19985 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____19985
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___262_20004 = g  in
            let uu____20005 =
              let uu____20006 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____20006  in
            {
              guard_f = uu____20005;
              deferred = (uu___262_20004.deferred);
              univ_ineqs = (uu___262_20004.univ_ineqs);
              implicits = (uu___262_20004.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,guard_t)
              FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            let uu____20044 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____20044 with
            | FStar_Pervasives_Native.Some
                (uu____20067::(tm,uu____20069)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____20119 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____20135 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____20135;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                   true gamma binders;
                 (let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_uvar
                         (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                      FStar_Pervasives_Native.None r
                     in
                  let g =
                    let uu___263_20165 = trivial_guard  in
                    {
                      guard_f = (uu___263_20165.guard_f);
                      deferred = (uu___263_20165.deferred);
                      univ_ineqs = (uu___263_20165.univ_ineqs);
                      implicits = [(reason, t, ctx_uvar, r)]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____20198  -> ());
    push = (fun uu____20200  -> ());
    pop = (fun uu____20202  -> ());
    snapshot =
      (fun uu____20204  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____20213  -> fun uu____20214  -> ());
    encode_modul = (fun uu____20225  -> fun uu____20226  -> ());
    encode_sig = (fun uu____20229  -> fun uu____20230  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____20236 =
             let uu____20243 = FStar_Options.peek ()  in (e, g, uu____20243)
              in
           [uu____20236]);
    solve = (fun uu____20259  -> fun uu____20260  -> fun uu____20261  -> ());
    finish = (fun uu____20267  -> ());
    refresh = (fun uu____20269  -> ())
  } 