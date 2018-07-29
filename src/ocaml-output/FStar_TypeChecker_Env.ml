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
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap ;
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
  phase1: Prims.bool ;
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
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range ;
  imp_meta:
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__attrtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__admit
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__lax
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__normalized_eff_names
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dsenv
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
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
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_range
  
let (__proj__Mkimplicit__item__imp_meta :
  implicit ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_meta
  
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
type implicits = implicit Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___221_9818  ->
              match uu___221_9818 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9821 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9821  in
                  let uu____9822 =
                    let uu____9823 = FStar_Syntax_Subst.compress y  in
                    uu____9823.FStar_Syntax_Syntax.n  in
                  (match uu____9822 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9827 =
                         let uu___235_9828 = y1  in
                         let uu____9829 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___235_9828.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___235_9828.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9829
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9827
                   | uu____9832 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___236_9844 = env  in
      let uu____9845 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___236_9844.solver);
        range = (uu___236_9844.range);
        curmodule = (uu___236_9844.curmodule);
        gamma = uu____9845;
        gamma_sig = (uu___236_9844.gamma_sig);
        gamma_cache = (uu___236_9844.gamma_cache);
        modules = (uu___236_9844.modules);
        expected_typ = (uu___236_9844.expected_typ);
        sigtab = (uu___236_9844.sigtab);
        attrtab = (uu___236_9844.attrtab);
        is_pattern = (uu___236_9844.is_pattern);
        instantiate_imp = (uu___236_9844.instantiate_imp);
        effects = (uu___236_9844.effects);
        generalize = (uu___236_9844.generalize);
        letrecs = (uu___236_9844.letrecs);
        top_level = (uu___236_9844.top_level);
        check_uvars = (uu___236_9844.check_uvars);
        use_eq = (uu___236_9844.use_eq);
        is_iface = (uu___236_9844.is_iface);
        admit = (uu___236_9844.admit);
        lax = (uu___236_9844.lax);
        lax_universes = (uu___236_9844.lax_universes);
        phase1 = (uu___236_9844.phase1);
        failhard = (uu___236_9844.failhard);
        nosynth = (uu___236_9844.nosynth);
        uvar_subtyping = (uu___236_9844.uvar_subtyping);
        tc_term = (uu___236_9844.tc_term);
        type_of = (uu___236_9844.type_of);
        universe_of = (uu___236_9844.universe_of);
        check_type_of = (uu___236_9844.check_type_of);
        use_bv_sorts = (uu___236_9844.use_bv_sorts);
        qtbl_name_and_index = (uu___236_9844.qtbl_name_and_index);
        normalized_eff_names = (uu___236_9844.normalized_eff_names);
        proof_ns = (uu___236_9844.proof_ns);
        synth_hook = (uu___236_9844.synth_hook);
        splice = (uu___236_9844.splice);
        is_native_tactic = (uu___236_9844.is_native_tactic);
        identifier_info = (uu___236_9844.identifier_info);
        tc_hooks = (uu___236_9844.tc_hooks);
        dsenv = (uu___236_9844.dsenv);
        dep_graph = (uu___236_9844.dep_graph);
        nbe = (uu___236_9844.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9852  -> fun uu____9853  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___237_9873 = env  in
      {
        solver = (uu___237_9873.solver);
        range = (uu___237_9873.range);
        curmodule = (uu___237_9873.curmodule);
        gamma = (uu___237_9873.gamma);
        gamma_sig = (uu___237_9873.gamma_sig);
        gamma_cache = (uu___237_9873.gamma_cache);
        modules = (uu___237_9873.modules);
        expected_typ = (uu___237_9873.expected_typ);
        sigtab = (uu___237_9873.sigtab);
        attrtab = (uu___237_9873.attrtab);
        is_pattern = (uu___237_9873.is_pattern);
        instantiate_imp = (uu___237_9873.instantiate_imp);
        effects = (uu___237_9873.effects);
        generalize = (uu___237_9873.generalize);
        letrecs = (uu___237_9873.letrecs);
        top_level = (uu___237_9873.top_level);
        check_uvars = (uu___237_9873.check_uvars);
        use_eq = (uu___237_9873.use_eq);
        is_iface = (uu___237_9873.is_iface);
        admit = (uu___237_9873.admit);
        lax = (uu___237_9873.lax);
        lax_universes = (uu___237_9873.lax_universes);
        phase1 = (uu___237_9873.phase1);
        failhard = (uu___237_9873.failhard);
        nosynth = (uu___237_9873.nosynth);
        uvar_subtyping = (uu___237_9873.uvar_subtyping);
        tc_term = (uu___237_9873.tc_term);
        type_of = (uu___237_9873.type_of);
        universe_of = (uu___237_9873.universe_of);
        check_type_of = (uu___237_9873.check_type_of);
        use_bv_sorts = (uu___237_9873.use_bv_sorts);
        qtbl_name_and_index = (uu___237_9873.qtbl_name_and_index);
        normalized_eff_names = (uu___237_9873.normalized_eff_names);
        proof_ns = (uu___237_9873.proof_ns);
        synth_hook = (uu___237_9873.synth_hook);
        splice = (uu___237_9873.splice);
        is_native_tactic = (uu___237_9873.is_native_tactic);
        identifier_info = (uu___237_9873.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___237_9873.dsenv);
        dep_graph = (uu___237_9873.dep_graph);
        nbe = (uu___237_9873.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___238_9884 = e  in
      {
        solver = (uu___238_9884.solver);
        range = (uu___238_9884.range);
        curmodule = (uu___238_9884.curmodule);
        gamma = (uu___238_9884.gamma);
        gamma_sig = (uu___238_9884.gamma_sig);
        gamma_cache = (uu___238_9884.gamma_cache);
        modules = (uu___238_9884.modules);
        expected_typ = (uu___238_9884.expected_typ);
        sigtab = (uu___238_9884.sigtab);
        attrtab = (uu___238_9884.attrtab);
        is_pattern = (uu___238_9884.is_pattern);
        instantiate_imp = (uu___238_9884.instantiate_imp);
        effects = (uu___238_9884.effects);
        generalize = (uu___238_9884.generalize);
        letrecs = (uu___238_9884.letrecs);
        top_level = (uu___238_9884.top_level);
        check_uvars = (uu___238_9884.check_uvars);
        use_eq = (uu___238_9884.use_eq);
        is_iface = (uu___238_9884.is_iface);
        admit = (uu___238_9884.admit);
        lax = (uu___238_9884.lax);
        lax_universes = (uu___238_9884.lax_universes);
        phase1 = (uu___238_9884.phase1);
        failhard = (uu___238_9884.failhard);
        nosynth = (uu___238_9884.nosynth);
        uvar_subtyping = (uu___238_9884.uvar_subtyping);
        tc_term = (uu___238_9884.tc_term);
        type_of = (uu___238_9884.type_of);
        universe_of = (uu___238_9884.universe_of);
        check_type_of = (uu___238_9884.check_type_of);
        use_bv_sorts = (uu___238_9884.use_bv_sorts);
        qtbl_name_and_index = (uu___238_9884.qtbl_name_and_index);
        normalized_eff_names = (uu___238_9884.normalized_eff_names);
        proof_ns = (uu___238_9884.proof_ns);
        synth_hook = (uu___238_9884.synth_hook);
        splice = (uu___238_9884.splice);
        is_native_tactic = (uu___238_9884.is_native_tactic);
        identifier_info = (uu___238_9884.identifier_info);
        tc_hooks = (uu___238_9884.tc_hooks);
        dsenv = (uu___238_9884.dsenv);
        dep_graph = g;
        nbe = (uu___238_9884.nbe)
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
      | (NoDelta ,uu____9907) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____9908,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____9909,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____9910 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____9919 . unit -> 'Auu____9919 FStar_Util.smap =
  fun uu____9926  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____9931 . unit -> 'Auu____9931 FStar_Util.smap =
  fun uu____9938  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____10072 = new_gamma_cache ()  in
                  let uu____10075 = new_sigtab ()  in
                  let uu____10078 = new_sigtab ()  in
                  let uu____10085 =
                    let uu____10098 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____10098, FStar_Pervasives_Native.None)  in
                  let uu____10113 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____10116 = FStar_Options.using_facts_from ()  in
                  let uu____10117 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____10120 = FStar_Syntax_DsEnv.empty_env ()  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10072;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10075;
                    attrtab = uu____10078;
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
                    phase1 = false;
                    failhard = false;
                    nosynth = false;
                    uvar_subtyping = true;
                    tc_term;
                    type_of;
                    universe_of;
                    check_type_of;
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu____10085;
                    normalized_eff_names = uu____10113;
                    proof_ns = uu____10116;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10156  -> false);
                    identifier_info = uu____10117;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10120;
                    dep_graph = deps;
                    nbe = nbe1
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____10256  ->
    let uu____10257 = FStar_ST.op_Bang query_indices  in
    match uu____10257 with
    | [] -> failwith "Empty query indices!"
    | uu____10307 ->
        let uu____10316 =
          let uu____10325 =
            let uu____10332 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10332  in
          let uu____10382 = FStar_ST.op_Bang query_indices  in uu____10325 ::
            uu____10382
           in
        FStar_ST.op_Colon_Equals query_indices uu____10316
  
let (pop_query_indices : unit -> unit) =
  fun uu____10471  ->
    let uu____10472 = FStar_ST.op_Bang query_indices  in
    match uu____10472 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10587  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10617  ->
    match uu____10617 with
    | (l,n1) ->
        let uu____10624 = FStar_ST.op_Bang query_indices  in
        (match uu____10624 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10735 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10754  ->
    let uu____10755 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10755
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10828 =
       let uu____10831 = FStar_ST.op_Bang stack  in env :: uu____10831  in
     FStar_ST.op_Colon_Equals stack uu____10828);
    (let uu___239_10880 = env  in
     let uu____10881 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____10884 = FStar_Util.smap_copy (sigtab env)  in
     let uu____10887 = FStar_Util.smap_copy (attrtab env)  in
     let uu____10894 =
       let uu____10907 =
         let uu____10910 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____10910  in
       let uu____10935 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____10907, uu____10935)  in
     let uu____10976 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____10979 =
       let uu____10982 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____10982  in
     {
       solver = (uu___239_10880.solver);
       range = (uu___239_10880.range);
       curmodule = (uu___239_10880.curmodule);
       gamma = (uu___239_10880.gamma);
       gamma_sig = (uu___239_10880.gamma_sig);
       gamma_cache = uu____10881;
       modules = (uu___239_10880.modules);
       expected_typ = (uu___239_10880.expected_typ);
       sigtab = uu____10884;
       attrtab = uu____10887;
       is_pattern = (uu___239_10880.is_pattern);
       instantiate_imp = (uu___239_10880.instantiate_imp);
       effects = (uu___239_10880.effects);
       generalize = (uu___239_10880.generalize);
       letrecs = (uu___239_10880.letrecs);
       top_level = (uu___239_10880.top_level);
       check_uvars = (uu___239_10880.check_uvars);
       use_eq = (uu___239_10880.use_eq);
       is_iface = (uu___239_10880.is_iface);
       admit = (uu___239_10880.admit);
       lax = (uu___239_10880.lax);
       lax_universes = (uu___239_10880.lax_universes);
       phase1 = (uu___239_10880.phase1);
       failhard = (uu___239_10880.failhard);
       nosynth = (uu___239_10880.nosynth);
       uvar_subtyping = (uu___239_10880.uvar_subtyping);
       tc_term = (uu___239_10880.tc_term);
       type_of = (uu___239_10880.type_of);
       universe_of = (uu___239_10880.universe_of);
       check_type_of = (uu___239_10880.check_type_of);
       use_bv_sorts = (uu___239_10880.use_bv_sorts);
       qtbl_name_and_index = uu____10894;
       normalized_eff_names = uu____10976;
       proof_ns = (uu___239_10880.proof_ns);
       synth_hook = (uu___239_10880.synth_hook);
       splice = (uu___239_10880.splice);
       is_native_tactic = (uu___239_10880.is_native_tactic);
       identifier_info = uu____10979;
       tc_hooks = (uu___239_10880.tc_hooks);
       dsenv = (uu___239_10880.dsenv);
       dep_graph = (uu___239_10880.dep_graph);
       nbe = (uu___239_10880.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11028  ->
    let uu____11029 = FStar_ST.op_Bang stack  in
    match uu____11029 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11083 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____11155  ->
           let uu____11156 = snapshot_stack env  in
           match uu____11156 with
           | (stack_depth,env1) ->
               let uu____11181 = snapshot_query_indices ()  in
               (match uu____11181 with
                | (query_indices_depth,()) ->
                    let uu____11205 = (env1.solver).snapshot msg  in
                    (match uu____11205 with
                     | (solver_depth,()) ->
                         let uu____11247 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11247 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___240_11293 = env1  in
                                 {
                                   solver = (uu___240_11293.solver);
                                   range = (uu___240_11293.range);
                                   curmodule = (uu___240_11293.curmodule);
                                   gamma = (uu___240_11293.gamma);
                                   gamma_sig = (uu___240_11293.gamma_sig);
                                   gamma_cache = (uu___240_11293.gamma_cache);
                                   modules = (uu___240_11293.modules);
                                   expected_typ =
                                     (uu___240_11293.expected_typ);
                                   sigtab = (uu___240_11293.sigtab);
                                   attrtab = (uu___240_11293.attrtab);
                                   is_pattern = (uu___240_11293.is_pattern);
                                   instantiate_imp =
                                     (uu___240_11293.instantiate_imp);
                                   effects = (uu___240_11293.effects);
                                   generalize = (uu___240_11293.generalize);
                                   letrecs = (uu___240_11293.letrecs);
                                   top_level = (uu___240_11293.top_level);
                                   check_uvars = (uu___240_11293.check_uvars);
                                   use_eq = (uu___240_11293.use_eq);
                                   is_iface = (uu___240_11293.is_iface);
                                   admit = (uu___240_11293.admit);
                                   lax = (uu___240_11293.lax);
                                   lax_universes =
                                     (uu___240_11293.lax_universes);
                                   phase1 = (uu___240_11293.phase1);
                                   failhard = (uu___240_11293.failhard);
                                   nosynth = (uu___240_11293.nosynth);
                                   uvar_subtyping =
                                     (uu___240_11293.uvar_subtyping);
                                   tc_term = (uu___240_11293.tc_term);
                                   type_of = (uu___240_11293.type_of);
                                   universe_of = (uu___240_11293.universe_of);
                                   check_type_of =
                                     (uu___240_11293.check_type_of);
                                   use_bv_sorts =
                                     (uu___240_11293.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___240_11293.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___240_11293.normalized_eff_names);
                                   proof_ns = (uu___240_11293.proof_ns);
                                   synth_hook = (uu___240_11293.synth_hook);
                                   splice = (uu___240_11293.splice);
                                   is_native_tactic =
                                     (uu___240_11293.is_native_tactic);
                                   identifier_info =
                                     (uu___240_11293.identifier_info);
                                   tc_hooks = (uu___240_11293.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___240_11293.dep_graph);
                                   nbe = (uu___240_11293.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11324  ->
             let uu____11325 =
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
             match uu____11325 with
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
                             ((let uu____11491 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11491
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11502 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11502
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11529,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11561 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11587  ->
                  match uu____11587 with
                  | (m,uu____11593) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11561 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___241_11601 = env  in
               {
                 solver = (uu___241_11601.solver);
                 range = (uu___241_11601.range);
                 curmodule = (uu___241_11601.curmodule);
                 gamma = (uu___241_11601.gamma);
                 gamma_sig = (uu___241_11601.gamma_sig);
                 gamma_cache = (uu___241_11601.gamma_cache);
                 modules = (uu___241_11601.modules);
                 expected_typ = (uu___241_11601.expected_typ);
                 sigtab = (uu___241_11601.sigtab);
                 attrtab = (uu___241_11601.attrtab);
                 is_pattern = (uu___241_11601.is_pattern);
                 instantiate_imp = (uu___241_11601.instantiate_imp);
                 effects = (uu___241_11601.effects);
                 generalize = (uu___241_11601.generalize);
                 letrecs = (uu___241_11601.letrecs);
                 top_level = (uu___241_11601.top_level);
                 check_uvars = (uu___241_11601.check_uvars);
                 use_eq = (uu___241_11601.use_eq);
                 is_iface = (uu___241_11601.is_iface);
                 admit = (uu___241_11601.admit);
                 lax = (uu___241_11601.lax);
                 lax_universes = (uu___241_11601.lax_universes);
                 phase1 = (uu___241_11601.phase1);
                 failhard = (uu___241_11601.failhard);
                 nosynth = (uu___241_11601.nosynth);
                 uvar_subtyping = (uu___241_11601.uvar_subtyping);
                 tc_term = (uu___241_11601.tc_term);
                 type_of = (uu___241_11601.type_of);
                 universe_of = (uu___241_11601.universe_of);
                 check_type_of = (uu___241_11601.check_type_of);
                 use_bv_sorts = (uu___241_11601.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___241_11601.normalized_eff_names);
                 proof_ns = (uu___241_11601.proof_ns);
                 synth_hook = (uu___241_11601.synth_hook);
                 splice = (uu___241_11601.splice);
                 is_native_tactic = (uu___241_11601.is_native_tactic);
                 identifier_info = (uu___241_11601.identifier_info);
                 tc_hooks = (uu___241_11601.tc_hooks);
                 dsenv = (uu___241_11601.dsenv);
                 dep_graph = (uu___241_11601.dep_graph);
                 nbe = (uu___241_11601.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11614,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___242_11623 = env  in
               {
                 solver = (uu___242_11623.solver);
                 range = (uu___242_11623.range);
                 curmodule = (uu___242_11623.curmodule);
                 gamma = (uu___242_11623.gamma);
                 gamma_sig = (uu___242_11623.gamma_sig);
                 gamma_cache = (uu___242_11623.gamma_cache);
                 modules = (uu___242_11623.modules);
                 expected_typ = (uu___242_11623.expected_typ);
                 sigtab = (uu___242_11623.sigtab);
                 attrtab = (uu___242_11623.attrtab);
                 is_pattern = (uu___242_11623.is_pattern);
                 instantiate_imp = (uu___242_11623.instantiate_imp);
                 effects = (uu___242_11623.effects);
                 generalize = (uu___242_11623.generalize);
                 letrecs = (uu___242_11623.letrecs);
                 top_level = (uu___242_11623.top_level);
                 check_uvars = (uu___242_11623.check_uvars);
                 use_eq = (uu___242_11623.use_eq);
                 is_iface = (uu___242_11623.is_iface);
                 admit = (uu___242_11623.admit);
                 lax = (uu___242_11623.lax);
                 lax_universes = (uu___242_11623.lax_universes);
                 phase1 = (uu___242_11623.phase1);
                 failhard = (uu___242_11623.failhard);
                 nosynth = (uu___242_11623.nosynth);
                 uvar_subtyping = (uu___242_11623.uvar_subtyping);
                 tc_term = (uu___242_11623.tc_term);
                 type_of = (uu___242_11623.type_of);
                 universe_of = (uu___242_11623.universe_of);
                 check_type_of = (uu___242_11623.check_type_of);
                 use_bv_sorts = (uu___242_11623.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___242_11623.normalized_eff_names);
                 proof_ns = (uu___242_11623.proof_ns);
                 synth_hook = (uu___242_11623.synth_hook);
                 splice = (uu___242_11623.splice);
                 is_native_tactic = (uu___242_11623.is_native_tactic);
                 identifier_info = (uu___242_11623.identifier_info);
                 tc_hooks = (uu___242_11623.tc_hooks);
                 dsenv = (uu___242_11623.dsenv);
                 dep_graph = (uu___242_11623.dep_graph);
                 nbe = (uu___242_11623.nbe)
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
        (let uu___243_11657 = e  in
         {
           solver = (uu___243_11657.solver);
           range = r;
           curmodule = (uu___243_11657.curmodule);
           gamma = (uu___243_11657.gamma);
           gamma_sig = (uu___243_11657.gamma_sig);
           gamma_cache = (uu___243_11657.gamma_cache);
           modules = (uu___243_11657.modules);
           expected_typ = (uu___243_11657.expected_typ);
           sigtab = (uu___243_11657.sigtab);
           attrtab = (uu___243_11657.attrtab);
           is_pattern = (uu___243_11657.is_pattern);
           instantiate_imp = (uu___243_11657.instantiate_imp);
           effects = (uu___243_11657.effects);
           generalize = (uu___243_11657.generalize);
           letrecs = (uu___243_11657.letrecs);
           top_level = (uu___243_11657.top_level);
           check_uvars = (uu___243_11657.check_uvars);
           use_eq = (uu___243_11657.use_eq);
           is_iface = (uu___243_11657.is_iface);
           admit = (uu___243_11657.admit);
           lax = (uu___243_11657.lax);
           lax_universes = (uu___243_11657.lax_universes);
           phase1 = (uu___243_11657.phase1);
           failhard = (uu___243_11657.failhard);
           nosynth = (uu___243_11657.nosynth);
           uvar_subtyping = (uu___243_11657.uvar_subtyping);
           tc_term = (uu___243_11657.tc_term);
           type_of = (uu___243_11657.type_of);
           universe_of = (uu___243_11657.universe_of);
           check_type_of = (uu___243_11657.check_type_of);
           use_bv_sorts = (uu___243_11657.use_bv_sorts);
           qtbl_name_and_index = (uu___243_11657.qtbl_name_and_index);
           normalized_eff_names = (uu___243_11657.normalized_eff_names);
           proof_ns = (uu___243_11657.proof_ns);
           synth_hook = (uu___243_11657.synth_hook);
           splice = (uu___243_11657.splice);
           is_native_tactic = (uu___243_11657.is_native_tactic);
           identifier_info = (uu___243_11657.identifier_info);
           tc_hooks = (uu___243_11657.tc_hooks);
           dsenv = (uu___243_11657.dsenv);
           dep_graph = (uu___243_11657.dep_graph);
           nbe = (uu___243_11657.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11673 =
        let uu____11674 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11674 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11673
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11728 =
          let uu____11729 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11729 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11728
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11783 =
          let uu____11784 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11784 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11783
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11838 =
        let uu____11839 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11839 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11838
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___244_11900 = env  in
      {
        solver = (uu___244_11900.solver);
        range = (uu___244_11900.range);
        curmodule = lid;
        gamma = (uu___244_11900.gamma);
        gamma_sig = (uu___244_11900.gamma_sig);
        gamma_cache = (uu___244_11900.gamma_cache);
        modules = (uu___244_11900.modules);
        expected_typ = (uu___244_11900.expected_typ);
        sigtab = (uu___244_11900.sigtab);
        attrtab = (uu___244_11900.attrtab);
        is_pattern = (uu___244_11900.is_pattern);
        instantiate_imp = (uu___244_11900.instantiate_imp);
        effects = (uu___244_11900.effects);
        generalize = (uu___244_11900.generalize);
        letrecs = (uu___244_11900.letrecs);
        top_level = (uu___244_11900.top_level);
        check_uvars = (uu___244_11900.check_uvars);
        use_eq = (uu___244_11900.use_eq);
        is_iface = (uu___244_11900.is_iface);
        admit = (uu___244_11900.admit);
        lax = (uu___244_11900.lax);
        lax_universes = (uu___244_11900.lax_universes);
        phase1 = (uu___244_11900.phase1);
        failhard = (uu___244_11900.failhard);
        nosynth = (uu___244_11900.nosynth);
        uvar_subtyping = (uu___244_11900.uvar_subtyping);
        tc_term = (uu___244_11900.tc_term);
        type_of = (uu___244_11900.type_of);
        universe_of = (uu___244_11900.universe_of);
        check_type_of = (uu___244_11900.check_type_of);
        use_bv_sorts = (uu___244_11900.use_bv_sorts);
        qtbl_name_and_index = (uu___244_11900.qtbl_name_and_index);
        normalized_eff_names = (uu___244_11900.normalized_eff_names);
        proof_ns = (uu___244_11900.proof_ns);
        synth_hook = (uu___244_11900.synth_hook);
        splice = (uu___244_11900.splice);
        is_native_tactic = (uu___244_11900.is_native_tactic);
        identifier_info = (uu___244_11900.identifier_info);
        tc_hooks = (uu___244_11900.tc_hooks);
        dsenv = (uu___244_11900.dsenv);
        dep_graph = (uu___244_11900.dep_graph);
        nbe = (uu___244_11900.nbe)
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
      let uu____11927 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11927
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11937 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11937)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11947 =
      let uu____11948 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11948  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11947)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11953  ->
    let uu____11954 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11954
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
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
      | ((formals,t),uu____12048) ->
          let vs = mk_univ_subst formals us  in
          let uu____12072 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12072)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___222_12088  ->
    match uu___222_12088 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12114  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universe Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun t  ->
      let uu____12135 = inst_tscheme t  in
      match uu____12135 with
      | (us,t1) ->
          let uu____12156 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12156)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12178  ->
          match uu____12178 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12199 =
                         let uu____12200 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12201 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12202 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12203 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12200 uu____12201 uu____12202 uu____12203
                          in
                       failwith uu____12199)
                    else ();
                    (let uu____12205 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12205))
               | uu____12214 ->
                   let uu____12215 =
                     let uu____12216 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12216
                      in
                   failwith uu____12215)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12222 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12228 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12234 -> false
  
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
             | ([],uu____12276) -> Maybe
             | (uu____12283,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12302 -> No  in
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
          let uu____12393 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12393 with
          | FStar_Pervasives_Native.None  ->
              let uu____12440 =
                FStar_Util.find_map env.gamma
                  (fun uu___223_12484  ->
                     match uu___223_12484 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12523 = FStar_Ident.lid_equals lid l  in
                         if uu____12523
                         then
                           let uu____12544 =
                             let uu____12563 =
                               let uu____12578 = inst_tscheme t  in
                               FStar_Util.Inl uu____12578  in
                             let uu____12593 = FStar_Ident.range_of_lid l  in
                             (uu____12563, uu____12593)  in
                           FStar_Pervasives_Native.Some uu____12544
                         else FStar_Pervasives_Native.None
                     | uu____12645 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12440
                (fun uu____12683  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___224_12692  ->
                        match uu___224_12692 with
                        | (uu____12695,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12697);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12698;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12699;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12700;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12701;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12721 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12721
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
                                  uu____12769 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12776 -> cache t  in
                            let uu____12777 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12777 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12783 =
                                   let uu____12784 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12784)
                                    in
                                 maybe_cache uu____12783)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12852 = find_in_sigtab env lid  in
         match uu____12852 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12932 = lookup_qname env lid  in
      match uu____12932 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12959,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13114 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13114 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13156 =
          let uu____13159 = lookup_attr env1 attr  in se1 :: uu____13159  in
        FStar_Util.smap_add (attrtab env1) attr uu____13156  in
      FStar_List.iter
        (fun attr  ->
           let uu____13169 =
             let uu____13170 = FStar_Syntax_Subst.compress attr  in
             uu____13170.FStar_Syntax_Syntax.n  in
           match uu____13169 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13174 =
                 let uu____13175 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13175.FStar_Ident.str  in
               add_one1 env se uu____13174
           | uu____13176 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13198) ->
          add_sigelts env ses
      | uu____13207 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
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
            | uu____13222 -> ()))

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
        (fun uu___225_13253  ->
           match uu___225_13253 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13271 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13332,lb::[]),uu____13334) ->
            let uu____13347 =
              let uu____13356 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13365 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13356, uu____13365)  in
            FStar_Pervasives_Native.Some uu____13347
        | FStar_Syntax_Syntax.Sig_let ((uu____13378,lbs),uu____13380) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13416 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13428 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13428
                     then
                       let uu____13439 =
                         let uu____13448 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13457 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13448, uu____13457)  in
                       FStar_Pervasives_Native.Some uu____13439
                     else FStar_Pervasives_Native.None)
        | uu____13479 -> FStar_Pervasives_Native.None
  
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
          let uu____13538 =
            let uu____13547 =
              let uu____13552 =
                let uu____13553 =
                  let uu____13556 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13556
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13553)  in
              inst_tscheme1 uu____13552  in
            (uu____13547, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13538
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13578,uu____13579) ->
          let uu____13608 =
            let uu____13617 =
              let uu____13622 =
                let uu____13623 =
                  let uu____13626 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13626  in
                (us, uu____13623)  in
              inst_tscheme1 uu____13622  in
            (uu____13617, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13608
      | uu____13645 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universe Prims.list,FStar_Syntax_Syntax.term'
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
        let mapper uu____13735 =
          match uu____13735 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13831,uvs,t,uu____13834,uu____13835,uu____13836);
                      FStar_Syntax_Syntax.sigrng = uu____13837;
                      FStar_Syntax_Syntax.sigquals = uu____13838;
                      FStar_Syntax_Syntax.sigmeta = uu____13839;
                      FStar_Syntax_Syntax.sigattrs = uu____13840;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13869 =
                     let uu____13878 = inst_tscheme1 (uvs, t)  in
                     (uu____13878, rng)  in
                   FStar_Pervasives_Native.Some uu____13869
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13902;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13904;
                      FStar_Syntax_Syntax.sigattrs = uu____13905;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13930 =
                     let uu____13931 = in_cur_mod env l  in uu____13931 = Yes
                      in
                   if uu____13930
                   then
                     let uu____13942 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13942
                      then
                        let uu____13955 =
                          let uu____13964 = inst_tscheme1 (uvs, t)  in
                          (uu____13964, rng)  in
                        FStar_Pervasives_Native.Some uu____13955
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13995 =
                        let uu____14004 = inst_tscheme1 (uvs, t)  in
                        (uu____14004, rng)  in
                      FStar_Pervasives_Native.Some uu____13995)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14029,uu____14030);
                      FStar_Syntax_Syntax.sigrng = uu____14031;
                      FStar_Syntax_Syntax.sigquals = uu____14032;
                      FStar_Syntax_Syntax.sigmeta = uu____14033;
                      FStar_Syntax_Syntax.sigattrs = uu____14034;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____14099 =
                          let uu____14108 = inst_tscheme1 (uvs, k)  in
                          (uu____14108, rng)  in
                        FStar_Pervasives_Native.Some uu____14099
                    | uu____14129 ->
                        let uu____14138 =
                          let uu____14147 =
                            let uu____14152 =
                              let uu____14153 =
                                let uu____14156 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14156
                                 in
                              (uvs, uu____14153)  in
                            inst_tscheme1 uu____14152  in
                          (uu____14147, rng)  in
                        FStar_Pervasives_Native.Some uu____14138)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14179,uu____14180);
                      FStar_Syntax_Syntax.sigrng = uu____14181;
                      FStar_Syntax_Syntax.sigquals = uu____14182;
                      FStar_Syntax_Syntax.sigmeta = uu____14183;
                      FStar_Syntax_Syntax.sigattrs = uu____14184;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14250 =
                          let uu____14259 = inst_tscheme_with (uvs, k) us  in
                          (uu____14259, rng)  in
                        FStar_Pervasives_Native.Some uu____14250
                    | uu____14280 ->
                        let uu____14289 =
                          let uu____14298 =
                            let uu____14303 =
                              let uu____14304 =
                                let uu____14307 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14307
                                 in
                              (uvs, uu____14304)  in
                            inst_tscheme_with uu____14303 us  in
                          (uu____14298, rng)  in
                        FStar_Pervasives_Native.Some uu____14289)
               | FStar_Util.Inr se ->
                   let uu____14343 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14364;
                          FStar_Syntax_Syntax.sigrng = uu____14365;
                          FStar_Syntax_Syntax.sigquals = uu____14366;
                          FStar_Syntax_Syntax.sigmeta = uu____14367;
                          FStar_Syntax_Syntax.sigattrs = uu____14368;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14383 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14343
                     (FStar_Util.map_option
                        (fun uu____14431  ->
                           match uu____14431 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14462 =
          let uu____14473 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14473 mapper  in
        match uu____14462 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14565 =
              let uu____14578 =
                let uu____14587 =
                  let uu___245_14590 = t  in
                  let uu____14593 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___245_14590.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14593;
                    FStar_Syntax_Syntax.vars =
                      (uu___245_14590.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14587)  in
              (uu____14578, r)  in
            FStar_Pervasives_Native.Some uu____14565
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14652 = lookup_qname env l  in
      match uu____14652 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14677 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14741 = try_lookup_bv env bv  in
      match uu____14741 with
      | FStar_Pervasives_Native.None  ->
          let uu____14758 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14758 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14779 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14780 =
            let uu____14781 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14781  in
          (uu____14779, uu____14780)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14802 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14802 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14880 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14880  in
          let uu____14881 =
            let uu____14890 =
              let uu____14895 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14895)  in
            (uu____14890, r1)  in
          FStar_Pervasives_Native.Some uu____14881
  
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
        let uu____14929 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14929 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14966,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14999 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14999  in
            let uu____15000 =
              let uu____15005 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____15005, r1)  in
            FStar_Pervasives_Native.Some uu____15000
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____15028 = try_lookup_lid env l  in
      match uu____15028 with
      | FStar_Pervasives_Native.None  ->
          let uu____15059 = name_not_found l  in
          let uu____15064 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15059 uu____15064
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___226_15112  ->
              match uu___226_15112 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____15114 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15133 = lookup_qname env lid  in
      match uu____15133 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15142,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15145;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15147;
              FStar_Syntax_Syntax.sigattrs = uu____15148;_},FStar_Pervasives_Native.None
            ),uu____15149)
          ->
          let uu____15228 =
            let uu____15235 =
              let uu____15236 =
                let uu____15239 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____15239 t  in
              (uvs, uu____15236)  in
            (uu____15235, q)  in
          FStar_Pervasives_Native.Some uu____15228
      | uu____15252 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15273 = lookup_qname env lid  in
      match uu____15273 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15278,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15281;
              FStar_Syntax_Syntax.sigquals = uu____15282;
              FStar_Syntax_Syntax.sigmeta = uu____15283;
              FStar_Syntax_Syntax.sigattrs = uu____15284;_},FStar_Pervasives_Native.None
            ),uu____15285)
          ->
          let uu____15364 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15364 (uvs, t)
      | uu____15369 ->
          let uu____15370 = name_not_found lid  in
          let uu____15375 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15370 uu____15375
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15394 = lookup_qname env lid  in
      match uu____15394 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15399,uvs,t,uu____15402,uu____15403,uu____15404);
              FStar_Syntax_Syntax.sigrng = uu____15405;
              FStar_Syntax_Syntax.sigquals = uu____15406;
              FStar_Syntax_Syntax.sigmeta = uu____15407;
              FStar_Syntax_Syntax.sigattrs = uu____15408;_},FStar_Pervasives_Native.None
            ),uu____15409)
          ->
          let uu____15492 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15492 (uvs, t)
      | uu____15497 ->
          let uu____15498 = name_not_found lid  in
          let uu____15503 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15498 uu____15503
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15524 = lookup_qname env lid  in
      match uu____15524 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15531,uu____15532,uu____15533,uu____15534,uu____15535,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15537;
              FStar_Syntax_Syntax.sigquals = uu____15538;
              FStar_Syntax_Syntax.sigmeta = uu____15539;
              FStar_Syntax_Syntax.sigattrs = uu____15540;_},uu____15541),uu____15542)
          -> (true, dcs)
      | uu____15649 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15662 = lookup_qname env lid  in
      match uu____15662 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15663,uu____15664,uu____15665,l,uu____15667,uu____15668);
              FStar_Syntax_Syntax.sigrng = uu____15669;
              FStar_Syntax_Syntax.sigquals = uu____15670;
              FStar_Syntax_Syntax.sigmeta = uu____15671;
              FStar_Syntax_Syntax.sigattrs = uu____15672;_},uu____15673),uu____15674)
          -> l
      | uu____15759 ->
          let uu____15760 =
            let uu____15761 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15761  in
          failwith uu____15760
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15810)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15883,lbs),uu____15885)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15913 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15913
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15945 -> FStar_Pervasives_Native.None)
        | uu____15950 -> FStar_Pervasives_Native.None
  
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
        let uu____15980 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15980
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____16005),uu____16006) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____16077 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____16098),uu____16099) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____16170 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____16191 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____16191
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____16210 = lookup_qname env ftv  in
      match uu____16210 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____16214) ->
          let uu____16281 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____16281 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____16306,t),r) ->
               let uu____16337 =
                 let uu____16338 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____16338 t  in
               FStar_Pervasives_Native.Some uu____16337)
      | uu____16339 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____16350 = try_lookup_effect_lid env ftv  in
      match uu____16350 with
      | FStar_Pervasives_Native.None  ->
          let uu____16355 = name_not_found ftv  in
          let uu____16360 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____16355 uu____16360
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
        let uu____16387 = lookup_qname env lid0  in
        match uu____16387 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____16398);
                FStar_Syntax_Syntax.sigrng = uu____16399;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____16401;
                FStar_Syntax_Syntax.sigattrs = uu____16402;_},FStar_Pervasives_Native.None
              ),uu____16403)
            ->
            let lid1 =
              let uu____16503 =
                let uu____16504 = FStar_Ident.range_of_lid lid  in
                let uu____16505 =
                  let uu____16506 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____16506  in
                FStar_Range.set_use_range uu____16504 uu____16505  in
              FStar_Ident.set_lid_range lid uu____16503  in
            let uu____16507 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___227_16511  ->
                      match uu___227_16511 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____16512 -> false))
               in
            if uu____16507
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____16526 =
                      let uu____16527 =
                        let uu____16528 = get_range env  in
                        FStar_Range.string_of_range uu____16528  in
                      let uu____16529 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____16530 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____16527 uu____16529 uu____16530
                       in
                    failwith uu____16526)
                  in
               match (binders, univs1) with
               | ([],uu____16547) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16572,uu____16573::uu____16574::uu____16575) ->
                   let uu____16596 =
                     let uu____16597 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____16598 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16597 uu____16598
                      in
                   failwith uu____16596
               | uu____16605 ->
                   let uu____16620 =
                     let uu____16625 =
                       let uu____16626 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____16626)  in
                     inst_tscheme_with uu____16625 insts  in
                   (match uu____16620 with
                    | (uu____16639,t) ->
                        let t1 =
                          let uu____16650 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16650 t  in
                        let uu____16651 =
                          let uu____16652 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16652.FStar_Syntax_Syntax.n  in
                        (match uu____16651 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16687 -> failwith "Impossible")))
        | uu____16694 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16717 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16717 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16740,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16777 = find1 l2  in
            (match uu____16777 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16784 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16784 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16788 = find1 l  in
            (match uu____16788 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16793 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16793
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16807 = lookup_qname env l1  in
      match uu____16807 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16810;
              FStar_Syntax_Syntax.sigrng = uu____16811;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16813;
              FStar_Syntax_Syntax.sigattrs = uu____16814;_},uu____16815),uu____16816)
          -> q
      | uu____16889 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16910 =
          let uu____16911 =
            let uu____16912 = FStar_Util.string_of_int i  in
            let uu____16913 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16912 uu____16913
             in
          failwith uu____16911  in
        let uu____16914 = lookup_datacon env lid  in
        match uu____16914 with
        | (uu____16919,t) ->
            let uu____16929 =
              let uu____16930 = FStar_Syntax_Subst.compress t  in
              uu____16930.FStar_Syntax_Syntax.n  in
            (match uu____16929 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16934) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16975 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16975
                      FStar_Pervasives_Native.fst)
             | uu____16986 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16997 = lookup_qname env l  in
      match uu____16997 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16998,uu____16999,uu____17000);
              FStar_Syntax_Syntax.sigrng = uu____17001;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____17003;
              FStar_Syntax_Syntax.sigattrs = uu____17004;_},uu____17005),uu____17006)
          ->
          FStar_Util.for_some
            (fun uu___228_17089  ->
               match uu___228_17089 with
               | FStar_Syntax_Syntax.Projector uu____17090 -> true
               | uu____17095 -> false) quals
      | uu____17096 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17107 = lookup_qname env lid  in
      match uu____17107 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17108,uu____17109,uu____17110,uu____17111,uu____17112,uu____17113);
              FStar_Syntax_Syntax.sigrng = uu____17114;
              FStar_Syntax_Syntax.sigquals = uu____17115;
              FStar_Syntax_Syntax.sigmeta = uu____17116;
              FStar_Syntax_Syntax.sigattrs = uu____17117;_},uu____17118),uu____17119)
          -> true
      | uu____17204 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17215 = lookup_qname env lid  in
      match uu____17215 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17216,uu____17217,uu____17218,uu____17219,uu____17220,uu____17221);
              FStar_Syntax_Syntax.sigrng = uu____17222;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____17224;
              FStar_Syntax_Syntax.sigattrs = uu____17225;_},uu____17226),uu____17227)
          ->
          FStar_Util.for_some
            (fun uu___229_17334  ->
               match uu___229_17334 with
               | FStar_Syntax_Syntax.RecordType uu____17335 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____17344 -> true
               | uu____17353 -> false) quals
      | uu____17354 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____17360,uu____17361);
            FStar_Syntax_Syntax.sigrng = uu____17362;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____17364;
            FStar_Syntax_Syntax.sigattrs = uu____17365;_},uu____17366),uu____17367)
        ->
        FStar_Util.for_some
          (fun uu___230_17458  ->
             match uu___230_17458 with
             | FStar_Syntax_Syntax.Action uu____17459 -> true
             | uu____17460 -> false) quals
    | uu____17461 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17472 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____17472
  
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
      let uu____17486 =
        let uu____17487 = FStar_Syntax_Util.un_uinst head1  in
        uu____17487.FStar_Syntax_Syntax.n  in
      match uu____17486 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____17491 ->
               true
           | uu____17492 -> false)
      | uu____17493 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17504 = lookup_qname env l  in
      match uu____17504 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____17506),uu____17507) ->
          FStar_Util.for_some
            (fun uu___231_17577  ->
               match uu___231_17577 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____17578 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____17579 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____17650 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____17666) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____17683 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____17690 ->
                 FStar_Pervasives_Native.Some true
             | uu____17707 -> FStar_Pervasives_Native.Some false)
         in
      let uu____17708 =
        let uu____17711 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____17711 mapper  in
      match uu____17708 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____17763 = lookup_qname env lid  in
      match uu____17763 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17766,uu____17767,tps,uu____17769,uu____17770,uu____17771);
              FStar_Syntax_Syntax.sigrng = uu____17772;
              FStar_Syntax_Syntax.sigquals = uu____17773;
              FStar_Syntax_Syntax.sigmeta = uu____17774;
              FStar_Syntax_Syntax.sigattrs = uu____17775;_},uu____17776),uu____17777)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____17888 -> FStar_Pervasives_Native.None
  
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
           (fun uu____17932  ->
              match uu____17932 with
              | (d,uu____17940) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17955 = effect_decl_opt env l  in
      match uu____17955 with
      | FStar_Pervasives_Native.None  ->
          let uu____17970 = name_not_found l  in
          let uu____17975 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17970 uu____17975
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17997  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____18016  ->
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
        let uu____18047 = FStar_Ident.lid_equals l1 l2  in
        if uu____18047
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____18055 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____18055
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____18063 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____18116  ->
                        match uu____18116 with
                        | (m1,m2,uu____18129,uu____18130,uu____18131) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____18063 with
              | FStar_Pervasives_Native.None  ->
                  let uu____18148 =
                    let uu____18153 =
                      let uu____18154 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____18155 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____18154
                        uu____18155
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____18153)
                     in
                  FStar_Errors.raise_error uu____18148 env.range
              | FStar_Pervasives_Native.Some
                  (uu____18162,uu____18163,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____18196 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____18196
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
  'Auu____18212 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____18212)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____18241 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____18267  ->
                match uu____18267 with
                | (d,uu____18273) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____18241 with
      | FStar_Pervasives_Native.None  ->
          let uu____18284 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____18284
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____18297 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____18297 with
           | (uu____18312,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____18338)::(wp,uu____18340)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____18396 -> failwith "Impossible"))
  
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
          let uu____18451 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____18451
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____18453 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____18453
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
                  let uu____18461 = get_range env  in
                  let uu____18462 =
                    let uu____18469 =
                      let uu____18470 =
                        let uu____18487 =
                          let uu____18498 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____18498]  in
                        (null_wp, uu____18487)  in
                      FStar_Syntax_Syntax.Tm_app uu____18470  in
                    FStar_Syntax_Syntax.mk uu____18469  in
                  uu____18462 FStar_Pervasives_Native.None uu____18461  in
                let uu____18538 =
                  let uu____18539 =
                    let uu____18550 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____18550]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____18539;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____18538))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___246_18587 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___246_18587.order);
              joins = (uu___246_18587.joins)
            }  in
          let uu___247_18596 = env  in
          {
            solver = (uu___247_18596.solver);
            range = (uu___247_18596.range);
            curmodule = (uu___247_18596.curmodule);
            gamma = (uu___247_18596.gamma);
            gamma_sig = (uu___247_18596.gamma_sig);
            gamma_cache = (uu___247_18596.gamma_cache);
            modules = (uu___247_18596.modules);
            expected_typ = (uu___247_18596.expected_typ);
            sigtab = (uu___247_18596.sigtab);
            attrtab = (uu___247_18596.attrtab);
            is_pattern = (uu___247_18596.is_pattern);
            instantiate_imp = (uu___247_18596.instantiate_imp);
            effects;
            generalize = (uu___247_18596.generalize);
            letrecs = (uu___247_18596.letrecs);
            top_level = (uu___247_18596.top_level);
            check_uvars = (uu___247_18596.check_uvars);
            use_eq = (uu___247_18596.use_eq);
            is_iface = (uu___247_18596.is_iface);
            admit = (uu___247_18596.admit);
            lax = (uu___247_18596.lax);
            lax_universes = (uu___247_18596.lax_universes);
            phase1 = (uu___247_18596.phase1);
            failhard = (uu___247_18596.failhard);
            nosynth = (uu___247_18596.nosynth);
            uvar_subtyping = (uu___247_18596.uvar_subtyping);
            tc_term = (uu___247_18596.tc_term);
            type_of = (uu___247_18596.type_of);
            universe_of = (uu___247_18596.universe_of);
            check_type_of = (uu___247_18596.check_type_of);
            use_bv_sorts = (uu___247_18596.use_bv_sorts);
            qtbl_name_and_index = (uu___247_18596.qtbl_name_and_index);
            normalized_eff_names = (uu___247_18596.normalized_eff_names);
            proof_ns = (uu___247_18596.proof_ns);
            synth_hook = (uu___247_18596.synth_hook);
            splice = (uu___247_18596.splice);
            is_native_tactic = (uu___247_18596.is_native_tactic);
            identifier_info = (uu___247_18596.identifier_info);
            tc_hooks = (uu___247_18596.tc_hooks);
            dsenv = (uu___247_18596.dsenv);
            dep_graph = (uu___247_18596.dep_graph);
            nbe = (uu___247_18596.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____18626 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____18626  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____18784 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____18785 = l1 u t wp e  in
                                l2 u t uu____18784 uu____18785))
                | uu____18786 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____18858 = inst_tscheme_with lift_t [u]  in
            match uu____18858 with
            | (uu____18865,lift_t1) ->
                let uu____18875 =
                  let uu____18882 =
                    let uu____18883 =
                      let uu____18900 =
                        let uu____18911 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18920 =
                          let uu____18931 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18931]  in
                        uu____18911 :: uu____18920  in
                      (lift_t1, uu____18900)  in
                    FStar_Syntax_Syntax.Tm_app uu____18883  in
                  FStar_Syntax_Syntax.mk uu____18882  in
                uu____18875 FStar_Pervasives_Native.None
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
            let uu____19067 = inst_tscheme_with lift_t [u]  in
            match uu____19067 with
            | (uu____19074,lift_t1) ->
                let uu____19084 =
                  let uu____19091 =
                    let uu____19092 =
                      let uu____19109 =
                        let uu____19120 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____19129 =
                          let uu____19140 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____19149 =
                            let uu____19160 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____19160]  in
                          uu____19140 :: uu____19149  in
                        uu____19120 :: uu____19129  in
                      (lift_t1, uu____19109)  in
                    FStar_Syntax_Syntax.Tm_app uu____19092  in
                  FStar_Syntax_Syntax.mk uu____19091  in
                uu____19084 FStar_Pervasives_Native.None
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
              let uu____19262 =
                let uu____19263 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____19263
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____19262  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____19267 =
              let uu____19268 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____19268  in
            let uu____19269 =
              let uu____19270 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____19296 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____19296)
                 in
              FStar_Util.dflt "none" uu____19270  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____19267
              uu____19269
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____19322  ->
                    match uu____19322 with
                    | (e,uu____19330) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____19353 =
            match uu____19353 with
            | (i,j) ->
                let uu____19364 = FStar_Ident.lid_equals i j  in
                if uu____19364
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
              let uu____19396 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____19406 = FStar_Ident.lid_equals i k  in
                        if uu____19406
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____19417 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____19417
                                  then []
                                  else
                                    (let uu____19421 =
                                       let uu____19430 =
                                         find_edge order1 (i, k)  in
                                       let uu____19433 =
                                         find_edge order1 (k, j)  in
                                       (uu____19430, uu____19433)  in
                                     match uu____19421 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____19448 =
                                           compose_edges e1 e2  in
                                         [uu____19448]
                                     | uu____19449 -> [])))))
                 in
              FStar_List.append order1 uu____19396  in
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
                   let uu____19479 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____19481 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____19481
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____19479
                   then
                     let uu____19486 =
                       let uu____19491 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____19491)
                        in
                     let uu____19492 = get_range env  in
                     FStar_Errors.raise_error uu____19486 uu____19492
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____19569 = FStar_Ident.lid_equals i j
                                   in
                                if uu____19569
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____19618 =
                                              let uu____19627 =
                                                find_edge order2 (i, k)  in
                                              let uu____19630 =
                                                find_edge order2 (j, k)  in
                                              (uu____19627, uu____19630)  in
                                            match uu____19618 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____19672,uu____19673)
                                                     ->
                                                     let uu____19680 =
                                                       let uu____19685 =
                                                         let uu____19686 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____19686
                                                          in
                                                       let uu____19689 =
                                                         let uu____19690 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____19690
                                                          in
                                                       (uu____19685,
                                                         uu____19689)
                                                        in
                                                     (match uu____19680 with
                                                      | (true ,true ) ->
                                                          let uu____19701 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____19701
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
                                            | uu____19726 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___248_19799 = env.effects  in
              { decls = (uu___248_19799.decls); order = order2; joins }  in
            let uu___249_19800 = env  in
            {
              solver = (uu___249_19800.solver);
              range = (uu___249_19800.range);
              curmodule = (uu___249_19800.curmodule);
              gamma = (uu___249_19800.gamma);
              gamma_sig = (uu___249_19800.gamma_sig);
              gamma_cache = (uu___249_19800.gamma_cache);
              modules = (uu___249_19800.modules);
              expected_typ = (uu___249_19800.expected_typ);
              sigtab = (uu___249_19800.sigtab);
              attrtab = (uu___249_19800.attrtab);
              is_pattern = (uu___249_19800.is_pattern);
              instantiate_imp = (uu___249_19800.instantiate_imp);
              effects;
              generalize = (uu___249_19800.generalize);
              letrecs = (uu___249_19800.letrecs);
              top_level = (uu___249_19800.top_level);
              check_uvars = (uu___249_19800.check_uvars);
              use_eq = (uu___249_19800.use_eq);
              is_iface = (uu___249_19800.is_iface);
              admit = (uu___249_19800.admit);
              lax = (uu___249_19800.lax);
              lax_universes = (uu___249_19800.lax_universes);
              phase1 = (uu___249_19800.phase1);
              failhard = (uu___249_19800.failhard);
              nosynth = (uu___249_19800.nosynth);
              uvar_subtyping = (uu___249_19800.uvar_subtyping);
              tc_term = (uu___249_19800.tc_term);
              type_of = (uu___249_19800.type_of);
              universe_of = (uu___249_19800.universe_of);
              check_type_of = (uu___249_19800.check_type_of);
              use_bv_sorts = (uu___249_19800.use_bv_sorts);
              qtbl_name_and_index = (uu___249_19800.qtbl_name_and_index);
              normalized_eff_names = (uu___249_19800.normalized_eff_names);
              proof_ns = (uu___249_19800.proof_ns);
              synth_hook = (uu___249_19800.synth_hook);
              splice = (uu___249_19800.splice);
              is_native_tactic = (uu___249_19800.is_native_tactic);
              identifier_info = (uu___249_19800.identifier_info);
              tc_hooks = (uu___249_19800.tc_hooks);
              dsenv = (uu___249_19800.dsenv);
              dep_graph = (uu___249_19800.dep_graph);
              nbe = (uu___249_19800.nbe)
            }))
      | uu____19801 -> env
  
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
        | uu____19829 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____19841 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____19841 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____19898 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____19898 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____19940 =
                     let uu____19945 =
                       let uu____19946 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____19953 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____19962 =
                         let uu____19963 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____19963  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____19946 uu____19953 uu____19962
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____19945)
                      in
                   FStar_Errors.raise_error uu____19940
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19968 =
                     let uu____19979 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____19979 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____20016  ->
                        fun uu____20017  ->
                          match (uu____20016, uu____20017) with
                          | ((x,uu____20047),(t,uu____20049)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19968
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____20080 =
                     let uu___250_20081 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___250_20081.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___250_20081.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___250_20081.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___250_20081.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____20080
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
          let uu____20111 = effect_decl_opt env effect_name  in
          match uu____20111 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____20144 =
                only_reifiable &&
                  (let uu____20146 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____20146)
                 in
              if uu____20144
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____20162 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____20185 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____20222 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____20222
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____20223 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____20223
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____20237 =
                       let uu____20240 = get_range env  in
                       let uu____20241 =
                         let uu____20248 =
                           let uu____20249 =
                             let uu____20266 =
                               let uu____20277 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____20277; wp]  in
                             (repr, uu____20266)  in
                           FStar_Syntax_Syntax.Tm_app uu____20249  in
                         FStar_Syntax_Syntax.mk uu____20248  in
                       uu____20241 FStar_Pervasives_Native.None uu____20240
                        in
                     FStar_Pervasives_Native.Some uu____20237)
  
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
          let uu____20367 =
            let uu____20372 =
              let uu____20373 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____20373
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____20372)  in
          let uu____20374 = get_range env  in
          FStar_Errors.raise_error uu____20367 uu____20374  in
        let uu____20375 = effect_repr_aux true env c u_c  in
        match uu____20375 with
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
      | uu____20421 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20432 =
        let uu____20433 = FStar_Syntax_Subst.compress t  in
        uu____20433.FStar_Syntax_Syntax.n  in
      match uu____20432 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____20436,c) ->
          is_reifiable_comp env c
      | uu____20458 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___251_20479 = env  in
        {
          solver = (uu___251_20479.solver);
          range = (uu___251_20479.range);
          curmodule = (uu___251_20479.curmodule);
          gamma = (uu___251_20479.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___251_20479.gamma_cache);
          modules = (uu___251_20479.modules);
          expected_typ = (uu___251_20479.expected_typ);
          sigtab = (uu___251_20479.sigtab);
          attrtab = (uu___251_20479.attrtab);
          is_pattern = (uu___251_20479.is_pattern);
          instantiate_imp = (uu___251_20479.instantiate_imp);
          effects = (uu___251_20479.effects);
          generalize = (uu___251_20479.generalize);
          letrecs = (uu___251_20479.letrecs);
          top_level = (uu___251_20479.top_level);
          check_uvars = (uu___251_20479.check_uvars);
          use_eq = (uu___251_20479.use_eq);
          is_iface = (uu___251_20479.is_iface);
          admit = (uu___251_20479.admit);
          lax = (uu___251_20479.lax);
          lax_universes = (uu___251_20479.lax_universes);
          phase1 = (uu___251_20479.phase1);
          failhard = (uu___251_20479.failhard);
          nosynth = (uu___251_20479.nosynth);
          uvar_subtyping = (uu___251_20479.uvar_subtyping);
          tc_term = (uu___251_20479.tc_term);
          type_of = (uu___251_20479.type_of);
          universe_of = (uu___251_20479.universe_of);
          check_type_of = (uu___251_20479.check_type_of);
          use_bv_sorts = (uu___251_20479.use_bv_sorts);
          qtbl_name_and_index = (uu___251_20479.qtbl_name_and_index);
          normalized_eff_names = (uu___251_20479.normalized_eff_names);
          proof_ns = (uu___251_20479.proof_ns);
          synth_hook = (uu___251_20479.synth_hook);
          splice = (uu___251_20479.splice);
          is_native_tactic = (uu___251_20479.is_native_tactic);
          identifier_info = (uu___251_20479.identifier_info);
          tc_hooks = (uu___251_20479.tc_hooks);
          dsenv = (uu___251_20479.dsenv);
          dep_graph = (uu___251_20479.dep_graph);
          nbe = (uu___251_20479.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___252_20492 = env  in
      {
        solver = (uu___252_20492.solver);
        range = (uu___252_20492.range);
        curmodule = (uu___252_20492.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___252_20492.gamma_sig);
        gamma_cache = (uu___252_20492.gamma_cache);
        modules = (uu___252_20492.modules);
        expected_typ = (uu___252_20492.expected_typ);
        sigtab = (uu___252_20492.sigtab);
        attrtab = (uu___252_20492.attrtab);
        is_pattern = (uu___252_20492.is_pattern);
        instantiate_imp = (uu___252_20492.instantiate_imp);
        effects = (uu___252_20492.effects);
        generalize = (uu___252_20492.generalize);
        letrecs = (uu___252_20492.letrecs);
        top_level = (uu___252_20492.top_level);
        check_uvars = (uu___252_20492.check_uvars);
        use_eq = (uu___252_20492.use_eq);
        is_iface = (uu___252_20492.is_iface);
        admit = (uu___252_20492.admit);
        lax = (uu___252_20492.lax);
        lax_universes = (uu___252_20492.lax_universes);
        phase1 = (uu___252_20492.phase1);
        failhard = (uu___252_20492.failhard);
        nosynth = (uu___252_20492.nosynth);
        uvar_subtyping = (uu___252_20492.uvar_subtyping);
        tc_term = (uu___252_20492.tc_term);
        type_of = (uu___252_20492.type_of);
        universe_of = (uu___252_20492.universe_of);
        check_type_of = (uu___252_20492.check_type_of);
        use_bv_sorts = (uu___252_20492.use_bv_sorts);
        qtbl_name_and_index = (uu___252_20492.qtbl_name_and_index);
        normalized_eff_names = (uu___252_20492.normalized_eff_names);
        proof_ns = (uu___252_20492.proof_ns);
        synth_hook = (uu___252_20492.synth_hook);
        splice = (uu___252_20492.splice);
        is_native_tactic = (uu___252_20492.is_native_tactic);
        identifier_info = (uu___252_20492.identifier_info);
        tc_hooks = (uu___252_20492.tc_hooks);
        dsenv = (uu___252_20492.dsenv);
        dep_graph = (uu___252_20492.dep_graph);
        nbe = (uu___252_20492.nbe)
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
            (let uu___253_20547 = env  in
             {
               solver = (uu___253_20547.solver);
               range = (uu___253_20547.range);
               curmodule = (uu___253_20547.curmodule);
               gamma = rest;
               gamma_sig = (uu___253_20547.gamma_sig);
               gamma_cache = (uu___253_20547.gamma_cache);
               modules = (uu___253_20547.modules);
               expected_typ = (uu___253_20547.expected_typ);
               sigtab = (uu___253_20547.sigtab);
               attrtab = (uu___253_20547.attrtab);
               is_pattern = (uu___253_20547.is_pattern);
               instantiate_imp = (uu___253_20547.instantiate_imp);
               effects = (uu___253_20547.effects);
               generalize = (uu___253_20547.generalize);
               letrecs = (uu___253_20547.letrecs);
               top_level = (uu___253_20547.top_level);
               check_uvars = (uu___253_20547.check_uvars);
               use_eq = (uu___253_20547.use_eq);
               is_iface = (uu___253_20547.is_iface);
               admit = (uu___253_20547.admit);
               lax = (uu___253_20547.lax);
               lax_universes = (uu___253_20547.lax_universes);
               phase1 = (uu___253_20547.phase1);
               failhard = (uu___253_20547.failhard);
               nosynth = (uu___253_20547.nosynth);
               uvar_subtyping = (uu___253_20547.uvar_subtyping);
               tc_term = (uu___253_20547.tc_term);
               type_of = (uu___253_20547.type_of);
               universe_of = (uu___253_20547.universe_of);
               check_type_of = (uu___253_20547.check_type_of);
               use_bv_sorts = (uu___253_20547.use_bv_sorts);
               qtbl_name_and_index = (uu___253_20547.qtbl_name_and_index);
               normalized_eff_names = (uu___253_20547.normalized_eff_names);
               proof_ns = (uu___253_20547.proof_ns);
               synth_hook = (uu___253_20547.synth_hook);
               splice = (uu___253_20547.splice);
               is_native_tactic = (uu___253_20547.is_native_tactic);
               identifier_info = (uu___253_20547.identifier_info);
               tc_hooks = (uu___253_20547.tc_hooks);
               dsenv = (uu___253_20547.dsenv);
               dep_graph = (uu___253_20547.dep_graph);
               nbe = (uu___253_20547.nbe)
             }))
    | uu____20548 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____20576  ->
             match uu____20576 with | (x,uu____20584) -> push_bv env1 x) env
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
            let uu___254_20618 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___254_20618.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___254_20618.FStar_Syntax_Syntax.index);
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
      (let uu___255_20658 = env  in
       {
         solver = (uu___255_20658.solver);
         range = (uu___255_20658.range);
         curmodule = (uu___255_20658.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___255_20658.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___255_20658.sigtab);
         attrtab = (uu___255_20658.attrtab);
         is_pattern = (uu___255_20658.is_pattern);
         instantiate_imp = (uu___255_20658.instantiate_imp);
         effects = (uu___255_20658.effects);
         generalize = (uu___255_20658.generalize);
         letrecs = (uu___255_20658.letrecs);
         top_level = (uu___255_20658.top_level);
         check_uvars = (uu___255_20658.check_uvars);
         use_eq = (uu___255_20658.use_eq);
         is_iface = (uu___255_20658.is_iface);
         admit = (uu___255_20658.admit);
         lax = (uu___255_20658.lax);
         lax_universes = (uu___255_20658.lax_universes);
         phase1 = (uu___255_20658.phase1);
         failhard = (uu___255_20658.failhard);
         nosynth = (uu___255_20658.nosynth);
         uvar_subtyping = (uu___255_20658.uvar_subtyping);
         tc_term = (uu___255_20658.tc_term);
         type_of = (uu___255_20658.type_of);
         universe_of = (uu___255_20658.universe_of);
         check_type_of = (uu___255_20658.check_type_of);
         use_bv_sorts = (uu___255_20658.use_bv_sorts);
         qtbl_name_and_index = (uu___255_20658.qtbl_name_and_index);
         normalized_eff_names = (uu___255_20658.normalized_eff_names);
         proof_ns = (uu___255_20658.proof_ns);
         synth_hook = (uu___255_20658.synth_hook);
         splice = (uu___255_20658.splice);
         is_native_tactic = (uu___255_20658.is_native_tactic);
         identifier_info = (uu___255_20658.identifier_info);
         tc_hooks = (uu___255_20658.tc_hooks);
         dsenv = (uu___255_20658.dsenv);
         dep_graph = (uu___255_20658.dep_graph);
         nbe = (uu___255_20658.nbe)
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
        let uu____20700 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____20700 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____20728 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____20728)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___256_20743 = env  in
      {
        solver = (uu___256_20743.solver);
        range = (uu___256_20743.range);
        curmodule = (uu___256_20743.curmodule);
        gamma = (uu___256_20743.gamma);
        gamma_sig = (uu___256_20743.gamma_sig);
        gamma_cache = (uu___256_20743.gamma_cache);
        modules = (uu___256_20743.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___256_20743.sigtab);
        attrtab = (uu___256_20743.attrtab);
        is_pattern = (uu___256_20743.is_pattern);
        instantiate_imp = (uu___256_20743.instantiate_imp);
        effects = (uu___256_20743.effects);
        generalize = (uu___256_20743.generalize);
        letrecs = (uu___256_20743.letrecs);
        top_level = (uu___256_20743.top_level);
        check_uvars = (uu___256_20743.check_uvars);
        use_eq = false;
        is_iface = (uu___256_20743.is_iface);
        admit = (uu___256_20743.admit);
        lax = (uu___256_20743.lax);
        lax_universes = (uu___256_20743.lax_universes);
        phase1 = (uu___256_20743.phase1);
        failhard = (uu___256_20743.failhard);
        nosynth = (uu___256_20743.nosynth);
        uvar_subtyping = (uu___256_20743.uvar_subtyping);
        tc_term = (uu___256_20743.tc_term);
        type_of = (uu___256_20743.type_of);
        universe_of = (uu___256_20743.universe_of);
        check_type_of = (uu___256_20743.check_type_of);
        use_bv_sorts = (uu___256_20743.use_bv_sorts);
        qtbl_name_and_index = (uu___256_20743.qtbl_name_and_index);
        normalized_eff_names = (uu___256_20743.normalized_eff_names);
        proof_ns = (uu___256_20743.proof_ns);
        synth_hook = (uu___256_20743.synth_hook);
        splice = (uu___256_20743.splice);
        is_native_tactic = (uu___256_20743.is_native_tactic);
        identifier_info = (uu___256_20743.identifier_info);
        tc_hooks = (uu___256_20743.tc_hooks);
        dsenv = (uu___256_20743.dsenv);
        dep_graph = (uu___256_20743.dep_graph);
        nbe = (uu___256_20743.nbe)
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
    let uu____20777 = expected_typ env_  in
    ((let uu___257_20783 = env_  in
      {
        solver = (uu___257_20783.solver);
        range = (uu___257_20783.range);
        curmodule = (uu___257_20783.curmodule);
        gamma = (uu___257_20783.gamma);
        gamma_sig = (uu___257_20783.gamma_sig);
        gamma_cache = (uu___257_20783.gamma_cache);
        modules = (uu___257_20783.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___257_20783.sigtab);
        attrtab = (uu___257_20783.attrtab);
        is_pattern = (uu___257_20783.is_pattern);
        instantiate_imp = (uu___257_20783.instantiate_imp);
        effects = (uu___257_20783.effects);
        generalize = (uu___257_20783.generalize);
        letrecs = (uu___257_20783.letrecs);
        top_level = (uu___257_20783.top_level);
        check_uvars = (uu___257_20783.check_uvars);
        use_eq = false;
        is_iface = (uu___257_20783.is_iface);
        admit = (uu___257_20783.admit);
        lax = (uu___257_20783.lax);
        lax_universes = (uu___257_20783.lax_universes);
        phase1 = (uu___257_20783.phase1);
        failhard = (uu___257_20783.failhard);
        nosynth = (uu___257_20783.nosynth);
        uvar_subtyping = (uu___257_20783.uvar_subtyping);
        tc_term = (uu___257_20783.tc_term);
        type_of = (uu___257_20783.type_of);
        universe_of = (uu___257_20783.universe_of);
        check_type_of = (uu___257_20783.check_type_of);
        use_bv_sorts = (uu___257_20783.use_bv_sorts);
        qtbl_name_and_index = (uu___257_20783.qtbl_name_and_index);
        normalized_eff_names = (uu___257_20783.normalized_eff_names);
        proof_ns = (uu___257_20783.proof_ns);
        synth_hook = (uu___257_20783.synth_hook);
        splice = (uu___257_20783.splice);
        is_native_tactic = (uu___257_20783.is_native_tactic);
        identifier_info = (uu___257_20783.identifier_info);
        tc_hooks = (uu___257_20783.tc_hooks);
        dsenv = (uu___257_20783.dsenv);
        dep_graph = (uu___257_20783.dep_graph);
        nbe = (uu___257_20783.nbe)
      }), uu____20777)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____20793 =
      let uu____20796 = FStar_Ident.id_of_text ""  in [uu____20796]  in
    FStar_Ident.lid_of_ids uu____20793  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____20802 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____20802
        then
          let uu____20805 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____20805 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___258_20832 = env  in
       {
         solver = (uu___258_20832.solver);
         range = (uu___258_20832.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___258_20832.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___258_20832.expected_typ);
         sigtab = (uu___258_20832.sigtab);
         attrtab = (uu___258_20832.attrtab);
         is_pattern = (uu___258_20832.is_pattern);
         instantiate_imp = (uu___258_20832.instantiate_imp);
         effects = (uu___258_20832.effects);
         generalize = (uu___258_20832.generalize);
         letrecs = (uu___258_20832.letrecs);
         top_level = (uu___258_20832.top_level);
         check_uvars = (uu___258_20832.check_uvars);
         use_eq = (uu___258_20832.use_eq);
         is_iface = (uu___258_20832.is_iface);
         admit = (uu___258_20832.admit);
         lax = (uu___258_20832.lax);
         lax_universes = (uu___258_20832.lax_universes);
         phase1 = (uu___258_20832.phase1);
         failhard = (uu___258_20832.failhard);
         nosynth = (uu___258_20832.nosynth);
         uvar_subtyping = (uu___258_20832.uvar_subtyping);
         tc_term = (uu___258_20832.tc_term);
         type_of = (uu___258_20832.type_of);
         universe_of = (uu___258_20832.universe_of);
         check_type_of = (uu___258_20832.check_type_of);
         use_bv_sorts = (uu___258_20832.use_bv_sorts);
         qtbl_name_and_index = (uu___258_20832.qtbl_name_and_index);
         normalized_eff_names = (uu___258_20832.normalized_eff_names);
         proof_ns = (uu___258_20832.proof_ns);
         synth_hook = (uu___258_20832.synth_hook);
         splice = (uu___258_20832.splice);
         is_native_tactic = (uu___258_20832.is_native_tactic);
         identifier_info = (uu___258_20832.identifier_info);
         tc_hooks = (uu___258_20832.tc_hooks);
         dsenv = (uu___258_20832.dsenv);
         dep_graph = (uu___258_20832.dep_graph);
         nbe = (uu___258_20832.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20883)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20887,(uu____20888,t)))::tl1
          ->
          let uu____20909 =
            let uu____20912 = FStar_Syntax_Free.uvars t  in
            ext out uu____20912  in
          aux uu____20909 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20915;
            FStar_Syntax_Syntax.index = uu____20916;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20923 =
            let uu____20926 = FStar_Syntax_Free.uvars t  in
            ext out uu____20926  in
          aux uu____20923 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20983)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20987,(uu____20988,t)))::tl1
          ->
          let uu____21009 =
            let uu____21012 = FStar_Syntax_Free.univs t  in
            ext out uu____21012  in
          aux uu____21009 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____21015;
            FStar_Syntax_Syntax.index = uu____21016;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____21023 =
            let uu____21026 = FStar_Syntax_Free.univs t  in
            ext out uu____21026  in
          aux uu____21023 tl1
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
          let uu____21087 = FStar_Util.set_add uname out  in
          aux uu____21087 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____21090,(uu____21091,t)))::tl1
          ->
          let uu____21112 =
            let uu____21115 = FStar_Syntax_Free.univnames t  in
            ext out uu____21115  in
          aux uu____21112 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____21118;
            FStar_Syntax_Syntax.index = uu____21119;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____21126 =
            let uu____21129 = FStar_Syntax_Free.univnames t  in
            ext out uu____21129  in
          aux uu____21126 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___232_21149  ->
            match uu___232_21149 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____21153 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____21166 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____21176 =
      let uu____21185 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____21185
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____21176 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____21229 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___233_21239  ->
              match uu___233_21239 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____21241 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____21241
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____21244) ->
                  let uu____21261 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____21261))
       in
    FStar_All.pipe_right uu____21229 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___234_21268  ->
    match uu___234_21268 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____21270 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____21270
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____21290  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____21332) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____21351,uu____21352) -> false  in
      let uu____21361 =
        FStar_List.tryFind
          (fun uu____21379  ->
             match uu____21379 with | (p,uu____21387) -> list_prefix p path)
          env.proof_ns
         in
      match uu____21361 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____21398,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21420 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____21420
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___259_21438 = e  in
        {
          solver = (uu___259_21438.solver);
          range = (uu___259_21438.range);
          curmodule = (uu___259_21438.curmodule);
          gamma = (uu___259_21438.gamma);
          gamma_sig = (uu___259_21438.gamma_sig);
          gamma_cache = (uu___259_21438.gamma_cache);
          modules = (uu___259_21438.modules);
          expected_typ = (uu___259_21438.expected_typ);
          sigtab = (uu___259_21438.sigtab);
          attrtab = (uu___259_21438.attrtab);
          is_pattern = (uu___259_21438.is_pattern);
          instantiate_imp = (uu___259_21438.instantiate_imp);
          effects = (uu___259_21438.effects);
          generalize = (uu___259_21438.generalize);
          letrecs = (uu___259_21438.letrecs);
          top_level = (uu___259_21438.top_level);
          check_uvars = (uu___259_21438.check_uvars);
          use_eq = (uu___259_21438.use_eq);
          is_iface = (uu___259_21438.is_iface);
          admit = (uu___259_21438.admit);
          lax = (uu___259_21438.lax);
          lax_universes = (uu___259_21438.lax_universes);
          phase1 = (uu___259_21438.phase1);
          failhard = (uu___259_21438.failhard);
          nosynth = (uu___259_21438.nosynth);
          uvar_subtyping = (uu___259_21438.uvar_subtyping);
          tc_term = (uu___259_21438.tc_term);
          type_of = (uu___259_21438.type_of);
          universe_of = (uu___259_21438.universe_of);
          check_type_of = (uu___259_21438.check_type_of);
          use_bv_sorts = (uu___259_21438.use_bv_sorts);
          qtbl_name_and_index = (uu___259_21438.qtbl_name_and_index);
          normalized_eff_names = (uu___259_21438.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___259_21438.synth_hook);
          splice = (uu___259_21438.splice);
          is_native_tactic = (uu___259_21438.is_native_tactic);
          identifier_info = (uu___259_21438.identifier_info);
          tc_hooks = (uu___259_21438.tc_hooks);
          dsenv = (uu___259_21438.dsenv);
          dep_graph = (uu___259_21438.dep_graph);
          nbe = (uu___259_21438.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___260_21478 = e  in
      {
        solver = (uu___260_21478.solver);
        range = (uu___260_21478.range);
        curmodule = (uu___260_21478.curmodule);
        gamma = (uu___260_21478.gamma);
        gamma_sig = (uu___260_21478.gamma_sig);
        gamma_cache = (uu___260_21478.gamma_cache);
        modules = (uu___260_21478.modules);
        expected_typ = (uu___260_21478.expected_typ);
        sigtab = (uu___260_21478.sigtab);
        attrtab = (uu___260_21478.attrtab);
        is_pattern = (uu___260_21478.is_pattern);
        instantiate_imp = (uu___260_21478.instantiate_imp);
        effects = (uu___260_21478.effects);
        generalize = (uu___260_21478.generalize);
        letrecs = (uu___260_21478.letrecs);
        top_level = (uu___260_21478.top_level);
        check_uvars = (uu___260_21478.check_uvars);
        use_eq = (uu___260_21478.use_eq);
        is_iface = (uu___260_21478.is_iface);
        admit = (uu___260_21478.admit);
        lax = (uu___260_21478.lax);
        lax_universes = (uu___260_21478.lax_universes);
        phase1 = (uu___260_21478.phase1);
        failhard = (uu___260_21478.failhard);
        nosynth = (uu___260_21478.nosynth);
        uvar_subtyping = (uu___260_21478.uvar_subtyping);
        tc_term = (uu___260_21478.tc_term);
        type_of = (uu___260_21478.type_of);
        universe_of = (uu___260_21478.universe_of);
        check_type_of = (uu___260_21478.check_type_of);
        use_bv_sorts = (uu___260_21478.use_bv_sorts);
        qtbl_name_and_index = (uu___260_21478.qtbl_name_and_index);
        normalized_eff_names = (uu___260_21478.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___260_21478.synth_hook);
        splice = (uu___260_21478.splice);
        is_native_tactic = (uu___260_21478.is_native_tactic);
        identifier_info = (uu___260_21478.identifier_info);
        tc_hooks = (uu___260_21478.tc_hooks);
        dsenv = (uu___260_21478.dsenv);
        dep_graph = (uu___260_21478.dep_graph);
        nbe = (uu___260_21478.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____21493 = FStar_Syntax_Free.names t  in
      let uu____21496 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____21493 uu____21496
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____21517 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____21517
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____21525 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____21525
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____21542 =
      match uu____21542 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____21552 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____21552)
       in
    let uu____21554 =
      let uu____21557 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____21557 FStar_List.rev  in
    FStar_All.pipe_right uu____21554 (FStar_String.concat " ")
  
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
             (fun imp  ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____21618 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____21618 with
                   | FStar_Pervasives_Native.Some uu____21621 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____21628 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____21634;
        univ_ineqs = uu____21635; implicits = uu____21636;_} -> true
    | uu____21647 -> false
  
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
          let uu___261_21674 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___261_21674.deferred);
            univ_ineqs = (uu___261_21674.univ_ineqs);
            implicits = (uu___261_21674.implicits)
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
          let uu____21709 = FStar_Options.defensive ()  in
          if uu____21709
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____21713 =
              let uu____21714 =
                let uu____21715 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____21715  in
              Prims.op_Negation uu____21714  in
            (if uu____21713
             then
               let uu____21720 =
                 let uu____21725 =
                   let uu____21726 = FStar_Syntax_Print.term_to_string t  in
                   let uu____21727 =
                     let uu____21728 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____21728
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____21726 uu____21727
                    in
                 (FStar_Errors.Warning_Defensive, uu____21725)  in
               FStar_Errors.log_issue rng uu____21720
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
          let uu____21759 =
            let uu____21760 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____21760  in
          if uu____21759
          then ()
          else
            (let uu____21762 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____21762 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____21785 =
            let uu____21786 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____21786  in
          if uu____21785
          then ()
          else
            (let uu____21788 = bound_vars e  in
             def_check_closed_in rng msg uu____21788 t)
  
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
          let uu___262_21823 = g  in
          let uu____21824 =
            let uu____21825 =
              let uu____21826 =
                let uu____21833 =
                  let uu____21834 =
                    let uu____21851 =
                      let uu____21862 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____21862]  in
                    (f, uu____21851)  in
                  FStar_Syntax_Syntax.Tm_app uu____21834  in
                FStar_Syntax_Syntax.mk uu____21833  in
              uu____21826 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____21825
             in
          {
            guard_f = uu____21824;
            deferred = (uu___262_21823.deferred);
            univ_ineqs = (uu___262_21823.univ_ineqs);
            implicits = (uu___262_21823.implicits)
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
          let uu___263_21918 = g  in
          let uu____21919 =
            let uu____21920 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____21920  in
          {
            guard_f = uu____21919;
            deferred = (uu___263_21918.deferred);
            univ_ineqs = (uu___263_21918.univ_ineqs);
            implicits = (uu___263_21918.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____21926 ->
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
          let uu____21941 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____21941
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____21947 =
      let uu____21948 = FStar_Syntax_Util.unmeta t  in
      uu____21948.FStar_Syntax_Syntax.n  in
    match uu____21947 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21952 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____21993 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____21993;
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
                       let uu____22074 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____22074
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___264_22078 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___264_22078.deferred);
              univ_ineqs = (uu___264_22078.univ_ineqs);
              implicits = (uu___264_22078.implicits)
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
               let uu____22111 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____22111
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
            let uu___265_22134 = g  in
            let uu____22135 =
              let uu____22136 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____22136  in
            {
              guard_f = uu____22135;
              deferred = (uu___265_22134.deferred);
              univ_ineqs = (uu___265_22134.univ_ineqs);
              implicits = (uu___265_22134.implicits)
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
            let uu____22174 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____22174 with
            | FStar_Pervasives_Native.Some
                (uu____22199::(tm,uu____22201)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____22265 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____22283 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____22283;
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
                  let imp =
                    {
                      imp_reason = reason;
                      imp_uvar = ctx_uvar;
                      imp_tm = t;
                      imp_range = r;
                      imp_meta = FStar_Pervasives_Native.None
                    }  in
                  let g =
                    let uu___266_22318 = trivial_guard  in
                    {
                      guard_f = (uu___266_22318.guard_f);
                      deferred = (uu___266_22318.deferred);
                      univ_ineqs = (uu___266_22318.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____22335  -> ());
    push = (fun uu____22337  -> ());
    pop = (fun uu____22339  -> ());
    snapshot =
      (fun uu____22341  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____22350  -> fun uu____22351  -> ());
    encode_modul = (fun uu____22362  -> fun uu____22363  -> ());
    encode_sig = (fun uu____22366  -> fun uu____22367  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____22373 =
             let uu____22380 = FStar_Options.peek ()  in (e, g, uu____22380)
              in
           [uu____22373]);
    solve = (fun uu____22396  -> fun uu____22397  -> fun uu____22398  -> ());
    finish = (fun uu____22404  -> ());
    refresh = (fun uu____22406  -> ())
  } 