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
           (fun uu___220_9818  ->
              match uu___220_9818 with
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
                         let uu___234_9828 = y1  in
                         let uu____9829 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___234_9828.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___234_9828.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9829
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9827
                   | uu____9832 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___235_9844 = env  in
      let uu____9845 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___235_9844.solver);
        range = (uu___235_9844.range);
        curmodule = (uu___235_9844.curmodule);
        gamma = uu____9845;
        gamma_sig = (uu___235_9844.gamma_sig);
        gamma_cache = (uu___235_9844.gamma_cache);
        modules = (uu___235_9844.modules);
        expected_typ = (uu___235_9844.expected_typ);
        sigtab = (uu___235_9844.sigtab);
        attrtab = (uu___235_9844.attrtab);
        is_pattern = (uu___235_9844.is_pattern);
        instantiate_imp = (uu___235_9844.instantiate_imp);
        effects = (uu___235_9844.effects);
        generalize = (uu___235_9844.generalize);
        letrecs = (uu___235_9844.letrecs);
        top_level = (uu___235_9844.top_level);
        check_uvars = (uu___235_9844.check_uvars);
        use_eq = (uu___235_9844.use_eq);
        is_iface = (uu___235_9844.is_iface);
        admit = (uu___235_9844.admit);
        lax = (uu___235_9844.lax);
        lax_universes = (uu___235_9844.lax_universes);
        phase1 = (uu___235_9844.phase1);
        failhard = (uu___235_9844.failhard);
        nosynth = (uu___235_9844.nosynth);
        uvar_subtyping = (uu___235_9844.uvar_subtyping);
        tc_term = (uu___235_9844.tc_term);
        type_of = (uu___235_9844.type_of);
        universe_of = (uu___235_9844.universe_of);
        check_type_of = (uu___235_9844.check_type_of);
        use_bv_sorts = (uu___235_9844.use_bv_sorts);
        qtbl_name_and_index = (uu___235_9844.qtbl_name_and_index);
        normalized_eff_names = (uu___235_9844.normalized_eff_names);
        proof_ns = (uu___235_9844.proof_ns);
        synth_hook = (uu___235_9844.synth_hook);
        splice = (uu___235_9844.splice);
        is_native_tactic = (uu___235_9844.is_native_tactic);
        identifier_info = (uu___235_9844.identifier_info);
        tc_hooks = (uu___235_9844.tc_hooks);
        dsenv = (uu___235_9844.dsenv);
        dep_graph = (uu___235_9844.dep_graph);
        nbe = (uu___235_9844.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9852  -> fun uu____9853  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___236_9873 = env  in
      {
        solver = (uu___236_9873.solver);
        range = (uu___236_9873.range);
        curmodule = (uu___236_9873.curmodule);
        gamma = (uu___236_9873.gamma);
        gamma_sig = (uu___236_9873.gamma_sig);
        gamma_cache = (uu___236_9873.gamma_cache);
        modules = (uu___236_9873.modules);
        expected_typ = (uu___236_9873.expected_typ);
        sigtab = (uu___236_9873.sigtab);
        attrtab = (uu___236_9873.attrtab);
        is_pattern = (uu___236_9873.is_pattern);
        instantiate_imp = (uu___236_9873.instantiate_imp);
        effects = (uu___236_9873.effects);
        generalize = (uu___236_9873.generalize);
        letrecs = (uu___236_9873.letrecs);
        top_level = (uu___236_9873.top_level);
        check_uvars = (uu___236_9873.check_uvars);
        use_eq = (uu___236_9873.use_eq);
        is_iface = (uu___236_9873.is_iface);
        admit = (uu___236_9873.admit);
        lax = (uu___236_9873.lax);
        lax_universes = (uu___236_9873.lax_universes);
        phase1 = (uu___236_9873.phase1);
        failhard = (uu___236_9873.failhard);
        nosynth = (uu___236_9873.nosynth);
        uvar_subtyping = (uu___236_9873.uvar_subtyping);
        tc_term = (uu___236_9873.tc_term);
        type_of = (uu___236_9873.type_of);
        universe_of = (uu___236_9873.universe_of);
        check_type_of = (uu___236_9873.check_type_of);
        use_bv_sorts = (uu___236_9873.use_bv_sorts);
        qtbl_name_and_index = (uu___236_9873.qtbl_name_and_index);
        normalized_eff_names = (uu___236_9873.normalized_eff_names);
        proof_ns = (uu___236_9873.proof_ns);
        synth_hook = (uu___236_9873.synth_hook);
        splice = (uu___236_9873.splice);
        is_native_tactic = (uu___236_9873.is_native_tactic);
        identifier_info = (uu___236_9873.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___236_9873.dsenv);
        dep_graph = (uu___236_9873.dep_graph);
        nbe = (uu___236_9873.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___237_9884 = e  in
      {
        solver = (uu___237_9884.solver);
        range = (uu___237_9884.range);
        curmodule = (uu___237_9884.curmodule);
        gamma = (uu___237_9884.gamma);
        gamma_sig = (uu___237_9884.gamma_sig);
        gamma_cache = (uu___237_9884.gamma_cache);
        modules = (uu___237_9884.modules);
        expected_typ = (uu___237_9884.expected_typ);
        sigtab = (uu___237_9884.sigtab);
        attrtab = (uu___237_9884.attrtab);
        is_pattern = (uu___237_9884.is_pattern);
        instantiate_imp = (uu___237_9884.instantiate_imp);
        effects = (uu___237_9884.effects);
        generalize = (uu___237_9884.generalize);
        letrecs = (uu___237_9884.letrecs);
        top_level = (uu___237_9884.top_level);
        check_uvars = (uu___237_9884.check_uvars);
        use_eq = (uu___237_9884.use_eq);
        is_iface = (uu___237_9884.is_iface);
        admit = (uu___237_9884.admit);
        lax = (uu___237_9884.lax);
        lax_universes = (uu___237_9884.lax_universes);
        phase1 = (uu___237_9884.phase1);
        failhard = (uu___237_9884.failhard);
        nosynth = (uu___237_9884.nosynth);
        uvar_subtyping = (uu___237_9884.uvar_subtyping);
        tc_term = (uu___237_9884.tc_term);
        type_of = (uu___237_9884.type_of);
        universe_of = (uu___237_9884.universe_of);
        check_type_of = (uu___237_9884.check_type_of);
        use_bv_sorts = (uu___237_9884.use_bv_sorts);
        qtbl_name_and_index = (uu___237_9884.qtbl_name_and_index);
        normalized_eff_names = (uu___237_9884.normalized_eff_names);
        proof_ns = (uu___237_9884.proof_ns);
        synth_hook = (uu___237_9884.synth_hook);
        splice = (uu___237_9884.splice);
        is_native_tactic = (uu___237_9884.is_native_tactic);
        identifier_info = (uu___237_9884.identifier_info);
        tc_hooks = (uu___237_9884.tc_hooks);
        dsenv = (uu___237_9884.dsenv);
        dep_graph = g;
        nbe = (uu___237_9884.nbe)
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
    (let uu___238_10880 = env  in
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
       solver = (uu___238_10880.solver);
       range = (uu___238_10880.range);
       curmodule = (uu___238_10880.curmodule);
       gamma = (uu___238_10880.gamma);
       gamma_sig = (uu___238_10880.gamma_sig);
       gamma_cache = uu____10881;
       modules = (uu___238_10880.modules);
       expected_typ = (uu___238_10880.expected_typ);
       sigtab = uu____10884;
       attrtab = uu____10887;
       is_pattern = (uu___238_10880.is_pattern);
       instantiate_imp = (uu___238_10880.instantiate_imp);
       effects = (uu___238_10880.effects);
       generalize = (uu___238_10880.generalize);
       letrecs = (uu___238_10880.letrecs);
       top_level = (uu___238_10880.top_level);
       check_uvars = (uu___238_10880.check_uvars);
       use_eq = (uu___238_10880.use_eq);
       is_iface = (uu___238_10880.is_iface);
       admit = (uu___238_10880.admit);
       lax = (uu___238_10880.lax);
       lax_universes = (uu___238_10880.lax_universes);
       phase1 = (uu___238_10880.phase1);
       failhard = (uu___238_10880.failhard);
       nosynth = (uu___238_10880.nosynth);
       uvar_subtyping = (uu___238_10880.uvar_subtyping);
       tc_term = (uu___238_10880.tc_term);
       type_of = (uu___238_10880.type_of);
       universe_of = (uu___238_10880.universe_of);
       check_type_of = (uu___238_10880.check_type_of);
       use_bv_sorts = (uu___238_10880.use_bv_sorts);
       qtbl_name_and_index = uu____10894;
       normalized_eff_names = uu____10976;
       proof_ns = (uu___238_10880.proof_ns);
       synth_hook = (uu___238_10880.synth_hook);
       splice = (uu___238_10880.splice);
       is_native_tactic = (uu___238_10880.is_native_tactic);
       identifier_info = uu____10979;
       tc_hooks = (uu___238_10880.tc_hooks);
       dsenv = (uu___238_10880.dsenv);
       dep_graph = (uu___238_10880.dep_graph);
       nbe = (uu___238_10880.nbe)
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
                                (let uu___239_11293 = env1  in
                                 {
                                   solver = (uu___239_11293.solver);
                                   range = (uu___239_11293.range);
                                   curmodule = (uu___239_11293.curmodule);
                                   gamma = (uu___239_11293.gamma);
                                   gamma_sig = (uu___239_11293.gamma_sig);
                                   gamma_cache = (uu___239_11293.gamma_cache);
                                   modules = (uu___239_11293.modules);
                                   expected_typ =
                                     (uu___239_11293.expected_typ);
                                   sigtab = (uu___239_11293.sigtab);
                                   attrtab = (uu___239_11293.attrtab);
                                   is_pattern = (uu___239_11293.is_pattern);
                                   instantiate_imp =
                                     (uu___239_11293.instantiate_imp);
                                   effects = (uu___239_11293.effects);
                                   generalize = (uu___239_11293.generalize);
                                   letrecs = (uu___239_11293.letrecs);
                                   top_level = (uu___239_11293.top_level);
                                   check_uvars = (uu___239_11293.check_uvars);
                                   use_eq = (uu___239_11293.use_eq);
                                   is_iface = (uu___239_11293.is_iface);
                                   admit = (uu___239_11293.admit);
                                   lax = (uu___239_11293.lax);
                                   lax_universes =
                                     (uu___239_11293.lax_universes);
                                   phase1 = (uu___239_11293.phase1);
                                   failhard = (uu___239_11293.failhard);
                                   nosynth = (uu___239_11293.nosynth);
                                   uvar_subtyping =
                                     (uu___239_11293.uvar_subtyping);
                                   tc_term = (uu___239_11293.tc_term);
                                   type_of = (uu___239_11293.type_of);
                                   universe_of = (uu___239_11293.universe_of);
                                   check_type_of =
                                     (uu___239_11293.check_type_of);
                                   use_bv_sorts =
                                     (uu___239_11293.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___239_11293.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___239_11293.normalized_eff_names);
                                   proof_ns = (uu___239_11293.proof_ns);
                                   synth_hook = (uu___239_11293.synth_hook);
                                   splice = (uu___239_11293.splice);
                                   is_native_tactic =
                                     (uu___239_11293.is_native_tactic);
                                   identifier_info =
                                     (uu___239_11293.identifier_info);
                                   tc_hooks = (uu___239_11293.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___239_11293.dep_graph);
                                   nbe = (uu___239_11293.nbe)
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
                             ((let uu____11451 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11451
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11462 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11462
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11489,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11521 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11547  ->
                  match uu____11547 with
                  | (m,uu____11553) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11521 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_11561 = env  in
               {
                 solver = (uu___240_11561.solver);
                 range = (uu___240_11561.range);
                 curmodule = (uu___240_11561.curmodule);
                 gamma = (uu___240_11561.gamma);
                 gamma_sig = (uu___240_11561.gamma_sig);
                 gamma_cache = (uu___240_11561.gamma_cache);
                 modules = (uu___240_11561.modules);
                 expected_typ = (uu___240_11561.expected_typ);
                 sigtab = (uu___240_11561.sigtab);
                 attrtab = (uu___240_11561.attrtab);
                 is_pattern = (uu___240_11561.is_pattern);
                 instantiate_imp = (uu___240_11561.instantiate_imp);
                 effects = (uu___240_11561.effects);
                 generalize = (uu___240_11561.generalize);
                 letrecs = (uu___240_11561.letrecs);
                 top_level = (uu___240_11561.top_level);
                 check_uvars = (uu___240_11561.check_uvars);
                 use_eq = (uu___240_11561.use_eq);
                 is_iface = (uu___240_11561.is_iface);
                 admit = (uu___240_11561.admit);
                 lax = (uu___240_11561.lax);
                 lax_universes = (uu___240_11561.lax_universes);
                 phase1 = (uu___240_11561.phase1);
                 failhard = (uu___240_11561.failhard);
                 nosynth = (uu___240_11561.nosynth);
                 uvar_subtyping = (uu___240_11561.uvar_subtyping);
                 tc_term = (uu___240_11561.tc_term);
                 type_of = (uu___240_11561.type_of);
                 universe_of = (uu___240_11561.universe_of);
                 check_type_of = (uu___240_11561.check_type_of);
                 use_bv_sorts = (uu___240_11561.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_11561.normalized_eff_names);
                 proof_ns = (uu___240_11561.proof_ns);
                 synth_hook = (uu___240_11561.synth_hook);
                 splice = (uu___240_11561.splice);
                 is_native_tactic = (uu___240_11561.is_native_tactic);
                 identifier_info = (uu___240_11561.identifier_info);
                 tc_hooks = (uu___240_11561.tc_hooks);
                 dsenv = (uu___240_11561.dsenv);
                 dep_graph = (uu___240_11561.dep_graph);
                 nbe = (uu___240_11561.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11574,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___241_11583 = env  in
               {
                 solver = (uu___241_11583.solver);
                 range = (uu___241_11583.range);
                 curmodule = (uu___241_11583.curmodule);
                 gamma = (uu___241_11583.gamma);
                 gamma_sig = (uu___241_11583.gamma_sig);
                 gamma_cache = (uu___241_11583.gamma_cache);
                 modules = (uu___241_11583.modules);
                 expected_typ = (uu___241_11583.expected_typ);
                 sigtab = (uu___241_11583.sigtab);
                 attrtab = (uu___241_11583.attrtab);
                 is_pattern = (uu___241_11583.is_pattern);
                 instantiate_imp = (uu___241_11583.instantiate_imp);
                 effects = (uu___241_11583.effects);
                 generalize = (uu___241_11583.generalize);
                 letrecs = (uu___241_11583.letrecs);
                 top_level = (uu___241_11583.top_level);
                 check_uvars = (uu___241_11583.check_uvars);
                 use_eq = (uu___241_11583.use_eq);
                 is_iface = (uu___241_11583.is_iface);
                 admit = (uu___241_11583.admit);
                 lax = (uu___241_11583.lax);
                 lax_universes = (uu___241_11583.lax_universes);
                 phase1 = (uu___241_11583.phase1);
                 failhard = (uu___241_11583.failhard);
                 nosynth = (uu___241_11583.nosynth);
                 uvar_subtyping = (uu___241_11583.uvar_subtyping);
                 tc_term = (uu___241_11583.tc_term);
                 type_of = (uu___241_11583.type_of);
                 universe_of = (uu___241_11583.universe_of);
                 check_type_of = (uu___241_11583.check_type_of);
                 use_bv_sorts = (uu___241_11583.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___241_11583.normalized_eff_names);
                 proof_ns = (uu___241_11583.proof_ns);
                 synth_hook = (uu___241_11583.synth_hook);
                 splice = (uu___241_11583.splice);
                 is_native_tactic = (uu___241_11583.is_native_tactic);
                 identifier_info = (uu___241_11583.identifier_info);
                 tc_hooks = (uu___241_11583.tc_hooks);
                 dsenv = (uu___241_11583.dsenv);
                 dep_graph = (uu___241_11583.dep_graph);
                 nbe = (uu___241_11583.nbe)
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
        (let uu___242_11617 = e  in
         {
           solver = (uu___242_11617.solver);
           range = r;
           curmodule = (uu___242_11617.curmodule);
           gamma = (uu___242_11617.gamma);
           gamma_sig = (uu___242_11617.gamma_sig);
           gamma_cache = (uu___242_11617.gamma_cache);
           modules = (uu___242_11617.modules);
           expected_typ = (uu___242_11617.expected_typ);
           sigtab = (uu___242_11617.sigtab);
           attrtab = (uu___242_11617.attrtab);
           is_pattern = (uu___242_11617.is_pattern);
           instantiate_imp = (uu___242_11617.instantiate_imp);
           effects = (uu___242_11617.effects);
           generalize = (uu___242_11617.generalize);
           letrecs = (uu___242_11617.letrecs);
           top_level = (uu___242_11617.top_level);
           check_uvars = (uu___242_11617.check_uvars);
           use_eq = (uu___242_11617.use_eq);
           is_iface = (uu___242_11617.is_iface);
           admit = (uu___242_11617.admit);
           lax = (uu___242_11617.lax);
           lax_universes = (uu___242_11617.lax_universes);
           phase1 = (uu___242_11617.phase1);
           failhard = (uu___242_11617.failhard);
           nosynth = (uu___242_11617.nosynth);
           uvar_subtyping = (uu___242_11617.uvar_subtyping);
           tc_term = (uu___242_11617.tc_term);
           type_of = (uu___242_11617.type_of);
           universe_of = (uu___242_11617.universe_of);
           check_type_of = (uu___242_11617.check_type_of);
           use_bv_sorts = (uu___242_11617.use_bv_sorts);
           qtbl_name_and_index = (uu___242_11617.qtbl_name_and_index);
           normalized_eff_names = (uu___242_11617.normalized_eff_names);
           proof_ns = (uu___242_11617.proof_ns);
           synth_hook = (uu___242_11617.synth_hook);
           splice = (uu___242_11617.splice);
           is_native_tactic = (uu___242_11617.is_native_tactic);
           identifier_info = (uu___242_11617.identifier_info);
           tc_hooks = (uu___242_11617.tc_hooks);
           dsenv = (uu___242_11617.dsenv);
           dep_graph = (uu___242_11617.dep_graph);
           nbe = (uu___242_11617.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11633 =
        let uu____11634 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11634 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11633
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11688 =
          let uu____11689 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11689 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11688
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11743 =
          let uu____11744 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11744 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11743
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11798 =
        let uu____11799 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11799 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11798
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___243_11860 = env  in
      {
        solver = (uu___243_11860.solver);
        range = (uu___243_11860.range);
        curmodule = lid;
        gamma = (uu___243_11860.gamma);
        gamma_sig = (uu___243_11860.gamma_sig);
        gamma_cache = (uu___243_11860.gamma_cache);
        modules = (uu___243_11860.modules);
        expected_typ = (uu___243_11860.expected_typ);
        sigtab = (uu___243_11860.sigtab);
        attrtab = (uu___243_11860.attrtab);
        is_pattern = (uu___243_11860.is_pattern);
        instantiate_imp = (uu___243_11860.instantiate_imp);
        effects = (uu___243_11860.effects);
        generalize = (uu___243_11860.generalize);
        letrecs = (uu___243_11860.letrecs);
        top_level = (uu___243_11860.top_level);
        check_uvars = (uu___243_11860.check_uvars);
        use_eq = (uu___243_11860.use_eq);
        is_iface = (uu___243_11860.is_iface);
        admit = (uu___243_11860.admit);
        lax = (uu___243_11860.lax);
        lax_universes = (uu___243_11860.lax_universes);
        phase1 = (uu___243_11860.phase1);
        failhard = (uu___243_11860.failhard);
        nosynth = (uu___243_11860.nosynth);
        uvar_subtyping = (uu___243_11860.uvar_subtyping);
        tc_term = (uu___243_11860.tc_term);
        type_of = (uu___243_11860.type_of);
        universe_of = (uu___243_11860.universe_of);
        check_type_of = (uu___243_11860.check_type_of);
        use_bv_sorts = (uu___243_11860.use_bv_sorts);
        qtbl_name_and_index = (uu___243_11860.qtbl_name_and_index);
        normalized_eff_names = (uu___243_11860.normalized_eff_names);
        proof_ns = (uu___243_11860.proof_ns);
        synth_hook = (uu___243_11860.synth_hook);
        splice = (uu___243_11860.splice);
        is_native_tactic = (uu___243_11860.is_native_tactic);
        identifier_info = (uu___243_11860.identifier_info);
        tc_hooks = (uu___243_11860.tc_hooks);
        dsenv = (uu___243_11860.dsenv);
        dep_graph = (uu___243_11860.dep_graph);
        nbe = (uu___243_11860.nbe)
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
      let uu____11887 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11887
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11897 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11897)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11907 =
      let uu____11908 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11908  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11907)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11913  ->
    let uu____11914 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11914
  
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
      | ((formals,t),uu____11970) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____12004 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12004)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___221_12020  ->
    match uu___221_12020 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12046  -> new_u_univ ()))
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
      let uu____12065 = inst_tscheme t  in
      match uu____12065 with
      | (us,t1) ->
          let uu____12076 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12076)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12096  ->
          match uu____12096 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12117 =
                         let uu____12118 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12119 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12120 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12121 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12118 uu____12119 uu____12120 uu____12121
                          in
                       failwith uu____12117)
                    else ();
                    (let uu____12123 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12123))
               | uu____12132 ->
                   let uu____12133 =
                     let uu____12134 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12134
                      in
                   failwith uu____12133)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12140 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12146 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12152 -> false
  
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
             | ([],uu____12194) -> Maybe
             | (uu____12201,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12220 -> No  in
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
          let uu____12311 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12311 with
          | FStar_Pervasives_Native.None  ->
              let uu____12334 =
                FStar_Util.find_map env.gamma
                  (fun uu___222_12378  ->
                     match uu___222_12378 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12417 = FStar_Ident.lid_equals lid l  in
                         if uu____12417
                         then
                           let uu____12438 =
                             let uu____12457 =
                               let uu____12472 = inst_tscheme t  in
                               FStar_Util.Inl uu____12472  in
                             let uu____12487 = FStar_Ident.range_of_lid l  in
                             (uu____12457, uu____12487)  in
                           FStar_Pervasives_Native.Some uu____12438
                         else FStar_Pervasives_Native.None
                     | uu____12539 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12334
                (fun uu____12577  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___223_12586  ->
                        match uu___223_12586 with
                        | (uu____12589,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12591);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12592;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12593;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12594;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12595;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12615 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12615
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
                                  uu____12663 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12670 -> cache t  in
                            let uu____12671 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12671 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12677 =
                                   let uu____12678 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12678)
                                    in
                                 maybe_cache uu____12677)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12746 = find_in_sigtab env lid  in
         match uu____12746 with
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
      let uu____12826 = lookup_qname env lid  in
      match uu____12826 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12847,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____12958 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____12958 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13000 =
          let uu____13003 = lookup_attr env1 attr  in se1 :: uu____13003  in
        FStar_Util.smap_add (attrtab env1) attr uu____13000  in
      FStar_List.iter
        (fun attr  ->
           let uu____13013 =
             let uu____13014 = FStar_Syntax_Subst.compress attr  in
             uu____13014.FStar_Syntax_Syntax.n  in
           match uu____13013 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13018 =
                 let uu____13019 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13019.FStar_Ident.str  in
               add_one1 env se uu____13018
           | uu____13020 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13042) ->
          add_sigelts env ses
      | uu____13051 ->
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
            | uu____13066 -> ()))

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
        (fun uu___224_13097  ->
           match uu___224_13097 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13115 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13176,lb::[]),uu____13178) ->
            let uu____13185 =
              let uu____13194 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13203 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13194, uu____13203)  in
            FStar_Pervasives_Native.Some uu____13185
        | FStar_Syntax_Syntax.Sig_let ((uu____13216,lbs),uu____13218) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13248 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13260 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13260
                     then
                       let uu____13271 =
                         let uu____13280 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13289 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13280, uu____13289)  in
                       FStar_Pervasives_Native.Some uu____13271
                     else FStar_Pervasives_Native.None)
        | uu____13311 -> FStar_Pervasives_Native.None
  
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
          let uu____13370 =
            let uu____13379 =
              let uu____13384 =
                let uu____13385 =
                  let uu____13388 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13388
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13385)  in
              inst_tscheme1 uu____13384  in
            (uu____13379, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13370
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13410,uu____13411) ->
          let uu____13416 =
            let uu____13425 =
              let uu____13430 =
                let uu____13431 =
                  let uu____13434 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13434  in
                (us, uu____13431)  in
              inst_tscheme1 uu____13430  in
            (uu____13425, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13416
      | uu____13453 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13541 =
          match uu____13541 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13637,uvs,t,uu____13640,uu____13641,uu____13642);
                      FStar_Syntax_Syntax.sigrng = uu____13643;
                      FStar_Syntax_Syntax.sigquals = uu____13644;
                      FStar_Syntax_Syntax.sigmeta = uu____13645;
                      FStar_Syntax_Syntax.sigattrs = uu____13646;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13667 =
                     let uu____13676 = inst_tscheme1 (uvs, t)  in
                     (uu____13676, rng)  in
                   FStar_Pervasives_Native.Some uu____13667
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13700;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13702;
                      FStar_Syntax_Syntax.sigattrs = uu____13703;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13720 =
                     let uu____13721 = in_cur_mod env l  in uu____13721 = Yes
                      in
                   if uu____13720
                   then
                     let uu____13732 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13732
                      then
                        let uu____13745 =
                          let uu____13754 = inst_tscheme1 (uvs, t)  in
                          (uu____13754, rng)  in
                        FStar_Pervasives_Native.Some uu____13745
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13785 =
                        let uu____13794 = inst_tscheme1 (uvs, t)  in
                        (uu____13794, rng)  in
                      FStar_Pervasives_Native.Some uu____13785)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13819,uu____13820);
                      FStar_Syntax_Syntax.sigrng = uu____13821;
                      FStar_Syntax_Syntax.sigquals = uu____13822;
                      FStar_Syntax_Syntax.sigmeta = uu____13823;
                      FStar_Syntax_Syntax.sigattrs = uu____13824;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13865 =
                          let uu____13874 = inst_tscheme1 (uvs, k)  in
                          (uu____13874, rng)  in
                        FStar_Pervasives_Native.Some uu____13865
                    | uu____13895 ->
                        let uu____13896 =
                          let uu____13905 =
                            let uu____13910 =
                              let uu____13911 =
                                let uu____13914 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13914
                                 in
                              (uvs, uu____13911)  in
                            inst_tscheme1 uu____13910  in
                          (uu____13905, rng)  in
                        FStar_Pervasives_Native.Some uu____13896)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13937,uu____13938);
                      FStar_Syntax_Syntax.sigrng = uu____13939;
                      FStar_Syntax_Syntax.sigquals = uu____13940;
                      FStar_Syntax_Syntax.sigmeta = uu____13941;
                      FStar_Syntax_Syntax.sigattrs = uu____13942;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13984 =
                          let uu____13993 = inst_tscheme_with (uvs, k) us  in
                          (uu____13993, rng)  in
                        FStar_Pervasives_Native.Some uu____13984
                    | uu____14014 ->
                        let uu____14015 =
                          let uu____14024 =
                            let uu____14029 =
                              let uu____14030 =
                                let uu____14033 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14033
                                 in
                              (uvs, uu____14030)  in
                            inst_tscheme_with uu____14029 us  in
                          (uu____14024, rng)  in
                        FStar_Pervasives_Native.Some uu____14015)
               | FStar_Util.Inr se ->
                   let uu____14069 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14090;
                          FStar_Syntax_Syntax.sigrng = uu____14091;
                          FStar_Syntax_Syntax.sigquals = uu____14092;
                          FStar_Syntax_Syntax.sigmeta = uu____14093;
                          FStar_Syntax_Syntax.sigattrs = uu____14094;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14109 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14069
                     (FStar_Util.map_option
                        (fun uu____14157  ->
                           match uu____14157 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14188 =
          let uu____14199 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14199 mapper  in
        match uu____14188 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14273 =
              let uu____14284 =
                let uu____14291 =
                  let uu___244_14294 = t  in
                  let uu____14295 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___244_14294.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14295;
                    FStar_Syntax_Syntax.vars =
                      (uu___244_14294.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14291)  in
              (uu____14284, r)  in
            FStar_Pervasives_Native.Some uu____14273
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14342 = lookup_qname env l  in
      match uu____14342 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14361 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14413 = try_lookup_bv env bv  in
      match uu____14413 with
      | FStar_Pervasives_Native.None  ->
          let uu____14428 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14428 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14443 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14444 =
            let uu____14445 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14445  in
          (uu____14443, uu____14444)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14466 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14466 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14532 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14532  in
          let uu____14533 =
            let uu____14542 =
              let uu____14547 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14547)  in
            (uu____14542, r1)  in
          FStar_Pervasives_Native.Some uu____14533
  
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
        let uu____14581 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14581 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14614,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14639 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14639  in
            let uu____14640 =
              let uu____14645 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14645, r1)  in
            FStar_Pervasives_Native.Some uu____14640
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14668 = try_lookup_lid env l  in
      match uu____14668 with
      | FStar_Pervasives_Native.None  ->
          let uu____14695 = name_not_found l  in
          let uu____14700 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14695 uu____14700
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___225_14740  ->
              match uu___225_14740 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14742 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14761 = lookup_qname env lid  in
      match uu____14761 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14770,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14773;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14775;
              FStar_Syntax_Syntax.sigattrs = uu____14776;_},FStar_Pervasives_Native.None
            ),uu____14777)
          ->
          let uu____14826 =
            let uu____14833 =
              let uu____14834 =
                let uu____14837 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14837 t  in
              (uvs, uu____14834)  in
            (uu____14833, q)  in
          FStar_Pervasives_Native.Some uu____14826
      | uu____14850 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14871 = lookup_qname env lid  in
      match uu____14871 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14876,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14879;
              FStar_Syntax_Syntax.sigquals = uu____14880;
              FStar_Syntax_Syntax.sigmeta = uu____14881;
              FStar_Syntax_Syntax.sigattrs = uu____14882;_},FStar_Pervasives_Native.None
            ),uu____14883)
          ->
          let uu____14932 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14932 (uvs, t)
      | uu____14937 ->
          let uu____14938 = name_not_found lid  in
          let uu____14943 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14938 uu____14943
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14962 = lookup_qname env lid  in
      match uu____14962 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14967,uvs,t,uu____14970,uu____14971,uu____14972);
              FStar_Syntax_Syntax.sigrng = uu____14973;
              FStar_Syntax_Syntax.sigquals = uu____14974;
              FStar_Syntax_Syntax.sigmeta = uu____14975;
              FStar_Syntax_Syntax.sigattrs = uu____14976;_},FStar_Pervasives_Native.None
            ),uu____14977)
          ->
          let uu____15030 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15030 (uvs, t)
      | uu____15035 ->
          let uu____15036 = name_not_found lid  in
          let uu____15041 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15036 uu____15041
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15062 = lookup_qname env lid  in
      match uu____15062 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15069,uu____15070,uu____15071,uu____15072,uu____15073,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15075;
              FStar_Syntax_Syntax.sigquals = uu____15076;
              FStar_Syntax_Syntax.sigmeta = uu____15077;
              FStar_Syntax_Syntax.sigattrs = uu____15078;_},uu____15079),uu____15080)
          -> (true, dcs)
      | uu____15141 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15154 = lookup_qname env lid  in
      match uu____15154 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15155,uu____15156,uu____15157,l,uu____15159,uu____15160);
              FStar_Syntax_Syntax.sigrng = uu____15161;
              FStar_Syntax_Syntax.sigquals = uu____15162;
              FStar_Syntax_Syntax.sigmeta = uu____15163;
              FStar_Syntax_Syntax.sigattrs = uu____15164;_},uu____15165),uu____15166)
          -> l
      | uu____15221 ->
          let uu____15222 =
            let uu____15223 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15223  in
          failwith uu____15222
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15272)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15323,lbs),uu____15325)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15347 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15347
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15379 -> FStar_Pervasives_Native.None)
        | uu____15384 -> FStar_Pervasives_Native.None
  
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
        let uu____15414 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15414
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15439),uu____15440) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15489 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15510),uu____15511) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15560 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15581 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15581
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15600 = lookup_qname env ftv  in
      match uu____15600 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15604) ->
          let uu____15649 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15649 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15670,t),r) ->
               let uu____15685 =
                 let uu____15686 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15686 t  in
               FStar_Pervasives_Native.Some uu____15685)
      | uu____15687 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15698 = try_lookup_effect_lid env ftv  in
      match uu____15698 with
      | FStar_Pervasives_Native.None  ->
          let uu____15701 = name_not_found ftv  in
          let uu____15706 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15701 uu____15706
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
        let uu____15729 = lookup_qname env lid0  in
        match uu____15729 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15740);
                FStar_Syntax_Syntax.sigrng = uu____15741;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15743;
                FStar_Syntax_Syntax.sigattrs = uu____15744;_},FStar_Pervasives_Native.None
              ),uu____15745)
            ->
            let lid1 =
              let uu____15799 =
                let uu____15800 = FStar_Ident.range_of_lid lid  in
                let uu____15801 =
                  let uu____15802 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____15802  in
                FStar_Range.set_use_range uu____15800 uu____15801  in
              FStar_Ident.set_lid_range lid uu____15799  in
            let uu____15803 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___226_15807  ->
                      match uu___226_15807 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____15808 -> false))
               in
            if uu____15803
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15822 =
                      let uu____15823 =
                        let uu____15824 = get_range env  in
                        FStar_Range.string_of_range uu____15824  in
                      let uu____15825 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____15826 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15823 uu____15825 uu____15826
                       in
                    failwith uu____15822)
                  in
               match (binders, univs1) with
               | ([],uu____15843) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____15868,uu____15869::uu____15870::uu____15871) ->
                   let uu____15892 =
                     let uu____15893 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____15894 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____15893 uu____15894
                      in
                   failwith uu____15892
               | uu____15901 ->
                   let uu____15916 =
                     let uu____15921 =
                       let uu____15922 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____15922)  in
                     inst_tscheme_with uu____15921 insts  in
                   (match uu____15916 with
                    | (uu____15935,t) ->
                        let t1 =
                          let uu____15938 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____15938 t  in
                        let uu____15939 =
                          let uu____15940 = FStar_Syntax_Subst.compress t1
                             in
                          uu____15940.FStar_Syntax_Syntax.n  in
                        (match uu____15939 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____15975 -> failwith "Impossible")))
        | uu____15982 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16005 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16005 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16018,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16025 = find1 l2  in
            (match uu____16025 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16032 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16032 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16036 = find1 l  in
            (match uu____16036 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16041 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16041
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16055 = lookup_qname env l1  in
      match uu____16055 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16058;
              FStar_Syntax_Syntax.sigrng = uu____16059;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16061;
              FStar_Syntax_Syntax.sigattrs = uu____16062;_},uu____16063),uu____16064)
          -> q
      | uu____16115 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16136 =
          let uu____16137 =
            let uu____16138 = FStar_Util.string_of_int i  in
            let uu____16139 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16138 uu____16139
             in
          failwith uu____16137  in
        let uu____16140 = lookup_datacon env lid  in
        match uu____16140 with
        | (uu____16145,t) ->
            let uu____16147 =
              let uu____16148 = FStar_Syntax_Subst.compress t  in
              uu____16148.FStar_Syntax_Syntax.n  in
            (match uu____16147 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16152) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16193 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16193
                      FStar_Pervasives_Native.fst)
             | uu____16204 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16215 = lookup_qname env l  in
      match uu____16215 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16216,uu____16217,uu____16218);
              FStar_Syntax_Syntax.sigrng = uu____16219;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16221;
              FStar_Syntax_Syntax.sigattrs = uu____16222;_},uu____16223),uu____16224)
          ->
          FStar_Util.for_some
            (fun uu___227_16277  ->
               match uu___227_16277 with
               | FStar_Syntax_Syntax.Projector uu____16278 -> true
               | uu____16283 -> false) quals
      | uu____16284 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16295 = lookup_qname env lid  in
      match uu____16295 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16296,uu____16297,uu____16298,uu____16299,uu____16300,uu____16301);
              FStar_Syntax_Syntax.sigrng = uu____16302;
              FStar_Syntax_Syntax.sigquals = uu____16303;
              FStar_Syntax_Syntax.sigmeta = uu____16304;
              FStar_Syntax_Syntax.sigattrs = uu____16305;_},uu____16306),uu____16307)
          -> true
      | uu____16362 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16373 = lookup_qname env lid  in
      match uu____16373 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16374,uu____16375,uu____16376,uu____16377,uu____16378,uu____16379);
              FStar_Syntax_Syntax.sigrng = uu____16380;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16382;
              FStar_Syntax_Syntax.sigattrs = uu____16383;_},uu____16384),uu____16385)
          ->
          FStar_Util.for_some
            (fun uu___228_16446  ->
               match uu___228_16446 with
               | FStar_Syntax_Syntax.RecordType uu____16447 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16456 -> true
               | uu____16465 -> false) quals
      | uu____16466 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16472,uu____16473);
            FStar_Syntax_Syntax.sigrng = uu____16474;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16476;
            FStar_Syntax_Syntax.sigattrs = uu____16477;_},uu____16478),uu____16479)
        ->
        FStar_Util.for_some
          (fun uu___229_16536  ->
             match uu___229_16536 with
             | FStar_Syntax_Syntax.Action uu____16537 -> true
             | uu____16538 -> false) quals
    | uu____16539 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16550 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16550
  
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
      let uu____16564 =
        let uu____16565 = FStar_Syntax_Util.un_uinst head1  in
        uu____16565.FStar_Syntax_Syntax.n  in
      match uu____16564 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16569 ->
               true
           | uu____16570 -> false)
      | uu____16571 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16582 = lookup_qname env l  in
      match uu____16582 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16584),uu____16585) ->
          FStar_Util.for_some
            (fun uu___230_16633  ->
               match uu___230_16633 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16634 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16635 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16706 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16722) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16739 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16746 ->
                 FStar_Pervasives_Native.Some true
             | uu____16763 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16764 =
        let uu____16767 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16767 mapper  in
      match uu____16764 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____16817 = lookup_qname env lid  in
      match uu____16817 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16818,uu____16819,tps,uu____16821,uu____16822,uu____16823);
              FStar_Syntax_Syntax.sigrng = uu____16824;
              FStar_Syntax_Syntax.sigquals = uu____16825;
              FStar_Syntax_Syntax.sigmeta = uu____16826;
              FStar_Syntax_Syntax.sigattrs = uu____16827;_},uu____16828),uu____16829)
          -> FStar_List.length tps
      | uu____16894 ->
          let uu____16895 = name_not_found lid  in
          let uu____16900 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____16895 uu____16900
  
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
           (fun uu____16944  ->
              match uu____16944 with
              | (d,uu____16952) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____16967 = effect_decl_opt env l  in
      match uu____16967 with
      | FStar_Pervasives_Native.None  ->
          let uu____16982 = name_not_found l  in
          let uu____16987 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____16982 uu____16987
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17009  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17028  ->
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
        let uu____17059 = FStar_Ident.lid_equals l1 l2  in
        if uu____17059
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17067 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17067
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17075 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17128  ->
                        match uu____17128 with
                        | (m1,m2,uu____17141,uu____17142,uu____17143) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17075 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17160 =
                    let uu____17165 =
                      let uu____17166 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17167 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17166
                        uu____17167
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17165)
                     in
                  FStar_Errors.raise_error uu____17160 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17174,uu____17175,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17208 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17208
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
  'Auu____17224 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17224)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17253 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17279  ->
                match uu____17279 with
                | (d,uu____17285) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17253 with
      | FStar_Pervasives_Native.None  ->
          let uu____17296 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17296
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17309 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17309 with
           | (uu____17324,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17342)::(wp,uu____17344)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17400 -> failwith "Impossible"))
  
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
          let uu____17455 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17455
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17457 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17457
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
                  let uu____17465 = get_range env  in
                  let uu____17466 =
                    let uu____17473 =
                      let uu____17474 =
                        let uu____17491 =
                          let uu____17502 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17502]  in
                        (null_wp, uu____17491)  in
                      FStar_Syntax_Syntax.Tm_app uu____17474  in
                    FStar_Syntax_Syntax.mk uu____17473  in
                  uu____17466 FStar_Pervasives_Native.None uu____17465  in
                let uu____17542 =
                  let uu____17543 =
                    let uu____17554 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17554]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17543;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17542))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___245_17591 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___245_17591.order);
              joins = (uu___245_17591.joins)
            }  in
          let uu___246_17600 = env  in
          {
            solver = (uu___246_17600.solver);
            range = (uu___246_17600.range);
            curmodule = (uu___246_17600.curmodule);
            gamma = (uu___246_17600.gamma);
            gamma_sig = (uu___246_17600.gamma_sig);
            gamma_cache = (uu___246_17600.gamma_cache);
            modules = (uu___246_17600.modules);
            expected_typ = (uu___246_17600.expected_typ);
            sigtab = (uu___246_17600.sigtab);
            attrtab = (uu___246_17600.attrtab);
            is_pattern = (uu___246_17600.is_pattern);
            instantiate_imp = (uu___246_17600.instantiate_imp);
            effects;
            generalize = (uu___246_17600.generalize);
            letrecs = (uu___246_17600.letrecs);
            top_level = (uu___246_17600.top_level);
            check_uvars = (uu___246_17600.check_uvars);
            use_eq = (uu___246_17600.use_eq);
            is_iface = (uu___246_17600.is_iface);
            admit = (uu___246_17600.admit);
            lax = (uu___246_17600.lax);
            lax_universes = (uu___246_17600.lax_universes);
            phase1 = (uu___246_17600.phase1);
            failhard = (uu___246_17600.failhard);
            nosynth = (uu___246_17600.nosynth);
            uvar_subtyping = (uu___246_17600.uvar_subtyping);
            tc_term = (uu___246_17600.tc_term);
            type_of = (uu___246_17600.type_of);
            universe_of = (uu___246_17600.universe_of);
            check_type_of = (uu___246_17600.check_type_of);
            use_bv_sorts = (uu___246_17600.use_bv_sorts);
            qtbl_name_and_index = (uu___246_17600.qtbl_name_and_index);
            normalized_eff_names = (uu___246_17600.normalized_eff_names);
            proof_ns = (uu___246_17600.proof_ns);
            synth_hook = (uu___246_17600.synth_hook);
            splice = (uu___246_17600.splice);
            is_native_tactic = (uu___246_17600.is_native_tactic);
            identifier_info = (uu___246_17600.identifier_info);
            tc_hooks = (uu___246_17600.tc_hooks);
            dsenv = (uu___246_17600.dsenv);
            dep_graph = (uu___246_17600.dep_graph);
            nbe = (uu___246_17600.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17630 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17630  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____17788 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____17789 = l1 u t wp e  in
                                l2 u t uu____17788 uu____17789))
                | uu____17790 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____17862 = inst_tscheme_with lift_t [u]  in
            match uu____17862 with
            | (uu____17869,lift_t1) ->
                let uu____17871 =
                  let uu____17878 =
                    let uu____17879 =
                      let uu____17896 =
                        let uu____17907 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17916 =
                          let uu____17927 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____17927]  in
                        uu____17907 :: uu____17916  in
                      (lift_t1, uu____17896)  in
                    FStar_Syntax_Syntax.Tm_app uu____17879  in
                  FStar_Syntax_Syntax.mk uu____17878  in
                uu____17871 FStar_Pervasives_Native.None
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
            let uu____18039 = inst_tscheme_with lift_t [u]  in
            match uu____18039 with
            | (uu____18046,lift_t1) ->
                let uu____18048 =
                  let uu____18055 =
                    let uu____18056 =
                      let uu____18073 =
                        let uu____18084 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18093 =
                          let uu____18104 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18113 =
                            let uu____18124 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18124]  in
                          uu____18104 :: uu____18113  in
                        uu____18084 :: uu____18093  in
                      (lift_t1, uu____18073)  in
                    FStar_Syntax_Syntax.Tm_app uu____18056  in
                  FStar_Syntax_Syntax.mk uu____18055  in
                uu____18048 FStar_Pervasives_Native.None
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
              let uu____18226 =
                let uu____18227 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18227
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18226  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18231 =
              let uu____18232 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18232  in
            let uu____18233 =
              let uu____18234 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18260 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18260)
                 in
              FStar_Util.dflt "none" uu____18234  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18231
              uu____18233
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18286  ->
                    match uu____18286 with
                    | (e,uu____18294) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18317 =
            match uu____18317 with
            | (i,j) ->
                let uu____18328 = FStar_Ident.lid_equals i j  in
                if uu____18328
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
              let uu____18360 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18370 = FStar_Ident.lid_equals i k  in
                        if uu____18370
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18381 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18381
                                  then []
                                  else
                                    (let uu____18385 =
                                       let uu____18394 =
                                         find_edge order1 (i, k)  in
                                       let uu____18397 =
                                         find_edge order1 (k, j)  in
                                       (uu____18394, uu____18397)  in
                                     match uu____18385 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18412 =
                                           compose_edges e1 e2  in
                                         [uu____18412]
                                     | uu____18413 -> [])))))
                 in
              FStar_List.append order1 uu____18360  in
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
                   let uu____18443 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18445 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18445
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18443
                   then
                     let uu____18450 =
                       let uu____18455 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18455)
                        in
                     let uu____18456 = get_range env  in
                     FStar_Errors.raise_error uu____18450 uu____18456
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18533 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18533
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18582 =
                                              let uu____18591 =
                                                find_edge order2 (i, k)  in
                                              let uu____18594 =
                                                find_edge order2 (j, k)  in
                                              (uu____18591, uu____18594)  in
                                            match uu____18582 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18636,uu____18637)
                                                     ->
                                                     let uu____18644 =
                                                       let uu____18649 =
                                                         let uu____18650 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18650
                                                          in
                                                       let uu____18653 =
                                                         let uu____18654 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18654
                                                          in
                                                       (uu____18649,
                                                         uu____18653)
                                                        in
                                                     (match uu____18644 with
                                                      | (true ,true ) ->
                                                          let uu____18665 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18665
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
                                            | uu____18690 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___247_18763 = env.effects  in
              { decls = (uu___247_18763.decls); order = order2; joins }  in
            let uu___248_18764 = env  in
            {
              solver = (uu___248_18764.solver);
              range = (uu___248_18764.range);
              curmodule = (uu___248_18764.curmodule);
              gamma = (uu___248_18764.gamma);
              gamma_sig = (uu___248_18764.gamma_sig);
              gamma_cache = (uu___248_18764.gamma_cache);
              modules = (uu___248_18764.modules);
              expected_typ = (uu___248_18764.expected_typ);
              sigtab = (uu___248_18764.sigtab);
              attrtab = (uu___248_18764.attrtab);
              is_pattern = (uu___248_18764.is_pattern);
              instantiate_imp = (uu___248_18764.instantiate_imp);
              effects;
              generalize = (uu___248_18764.generalize);
              letrecs = (uu___248_18764.letrecs);
              top_level = (uu___248_18764.top_level);
              check_uvars = (uu___248_18764.check_uvars);
              use_eq = (uu___248_18764.use_eq);
              is_iface = (uu___248_18764.is_iface);
              admit = (uu___248_18764.admit);
              lax = (uu___248_18764.lax);
              lax_universes = (uu___248_18764.lax_universes);
              phase1 = (uu___248_18764.phase1);
              failhard = (uu___248_18764.failhard);
              nosynth = (uu___248_18764.nosynth);
              uvar_subtyping = (uu___248_18764.uvar_subtyping);
              tc_term = (uu___248_18764.tc_term);
              type_of = (uu___248_18764.type_of);
              universe_of = (uu___248_18764.universe_of);
              check_type_of = (uu___248_18764.check_type_of);
              use_bv_sorts = (uu___248_18764.use_bv_sorts);
              qtbl_name_and_index = (uu___248_18764.qtbl_name_and_index);
              normalized_eff_names = (uu___248_18764.normalized_eff_names);
              proof_ns = (uu___248_18764.proof_ns);
              synth_hook = (uu___248_18764.synth_hook);
              splice = (uu___248_18764.splice);
              is_native_tactic = (uu___248_18764.is_native_tactic);
              identifier_info = (uu___248_18764.identifier_info);
              tc_hooks = (uu___248_18764.tc_hooks);
              dsenv = (uu___248_18764.dsenv);
              dep_graph = (uu___248_18764.dep_graph);
              nbe = (uu___248_18764.nbe)
            }))
      | uu____18765 -> env
  
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
        | uu____18793 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____18805 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____18805 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____18822 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____18822 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18844 =
                     let uu____18849 =
                       let uu____18850 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____18857 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____18866 =
                         let uu____18867 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____18867  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18850 uu____18857 uu____18866
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18849)
                      in
                   FStar_Errors.raise_error uu____18844
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____18872 =
                     let uu____18883 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____18883 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____18920  ->
                        fun uu____18921  ->
                          match (uu____18920, uu____18921) with
                          | ((x,uu____18951),(t,uu____18953)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____18872
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____18984 =
                     let uu___249_18985 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___249_18985.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___249_18985.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___249_18985.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___249_18985.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____18984
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
          let uu____19015 = effect_decl_opt env effect_name  in
          match uu____19015 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____19048 =
                only_reifiable &&
                  (let uu____19050 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____19050)
                 in
              if uu____19048
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____19066 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____19089 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____19126 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____19126
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____19127 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____19127
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____19141 =
                       let uu____19144 = get_range env  in
                       let uu____19145 =
                         let uu____19152 =
                           let uu____19153 =
                             let uu____19170 =
                               let uu____19181 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____19181; wp]  in
                             (repr, uu____19170)  in
                           FStar_Syntax_Syntax.Tm_app uu____19153  in
                         FStar_Syntax_Syntax.mk uu____19152  in
                       uu____19145 FStar_Pervasives_Native.None uu____19144
                        in
                     FStar_Pervasives_Native.Some uu____19141)
  
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
          let uu____19271 =
            let uu____19276 =
              let uu____19277 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____19277
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____19276)  in
          let uu____19278 = get_range env  in
          FStar_Errors.raise_error uu____19271 uu____19278  in
        let uu____19279 = effect_repr_aux true env c u_c  in
        match uu____19279 with
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
      | uu____19325 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19336 =
        let uu____19337 = FStar_Syntax_Subst.compress t  in
        uu____19337.FStar_Syntax_Syntax.n  in
      match uu____19336 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19340,c) ->
          is_reifiable_comp env c
      | uu____19362 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___250_19383 = env  in
        {
          solver = (uu___250_19383.solver);
          range = (uu___250_19383.range);
          curmodule = (uu___250_19383.curmodule);
          gamma = (uu___250_19383.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___250_19383.gamma_cache);
          modules = (uu___250_19383.modules);
          expected_typ = (uu___250_19383.expected_typ);
          sigtab = (uu___250_19383.sigtab);
          attrtab = (uu___250_19383.attrtab);
          is_pattern = (uu___250_19383.is_pattern);
          instantiate_imp = (uu___250_19383.instantiate_imp);
          effects = (uu___250_19383.effects);
          generalize = (uu___250_19383.generalize);
          letrecs = (uu___250_19383.letrecs);
          top_level = (uu___250_19383.top_level);
          check_uvars = (uu___250_19383.check_uvars);
          use_eq = (uu___250_19383.use_eq);
          is_iface = (uu___250_19383.is_iface);
          admit = (uu___250_19383.admit);
          lax = (uu___250_19383.lax);
          lax_universes = (uu___250_19383.lax_universes);
          phase1 = (uu___250_19383.phase1);
          failhard = (uu___250_19383.failhard);
          nosynth = (uu___250_19383.nosynth);
          uvar_subtyping = (uu___250_19383.uvar_subtyping);
          tc_term = (uu___250_19383.tc_term);
          type_of = (uu___250_19383.type_of);
          universe_of = (uu___250_19383.universe_of);
          check_type_of = (uu___250_19383.check_type_of);
          use_bv_sorts = (uu___250_19383.use_bv_sorts);
          qtbl_name_and_index = (uu___250_19383.qtbl_name_and_index);
          normalized_eff_names = (uu___250_19383.normalized_eff_names);
          proof_ns = (uu___250_19383.proof_ns);
          synth_hook = (uu___250_19383.synth_hook);
          splice = (uu___250_19383.splice);
          is_native_tactic = (uu___250_19383.is_native_tactic);
          identifier_info = (uu___250_19383.identifier_info);
          tc_hooks = (uu___250_19383.tc_hooks);
          dsenv = (uu___250_19383.dsenv);
          dep_graph = (uu___250_19383.dep_graph);
          nbe = (uu___250_19383.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___251_19396 = env  in
      {
        solver = (uu___251_19396.solver);
        range = (uu___251_19396.range);
        curmodule = (uu___251_19396.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___251_19396.gamma_sig);
        gamma_cache = (uu___251_19396.gamma_cache);
        modules = (uu___251_19396.modules);
        expected_typ = (uu___251_19396.expected_typ);
        sigtab = (uu___251_19396.sigtab);
        attrtab = (uu___251_19396.attrtab);
        is_pattern = (uu___251_19396.is_pattern);
        instantiate_imp = (uu___251_19396.instantiate_imp);
        effects = (uu___251_19396.effects);
        generalize = (uu___251_19396.generalize);
        letrecs = (uu___251_19396.letrecs);
        top_level = (uu___251_19396.top_level);
        check_uvars = (uu___251_19396.check_uvars);
        use_eq = (uu___251_19396.use_eq);
        is_iface = (uu___251_19396.is_iface);
        admit = (uu___251_19396.admit);
        lax = (uu___251_19396.lax);
        lax_universes = (uu___251_19396.lax_universes);
        phase1 = (uu___251_19396.phase1);
        failhard = (uu___251_19396.failhard);
        nosynth = (uu___251_19396.nosynth);
        uvar_subtyping = (uu___251_19396.uvar_subtyping);
        tc_term = (uu___251_19396.tc_term);
        type_of = (uu___251_19396.type_of);
        universe_of = (uu___251_19396.universe_of);
        check_type_of = (uu___251_19396.check_type_of);
        use_bv_sorts = (uu___251_19396.use_bv_sorts);
        qtbl_name_and_index = (uu___251_19396.qtbl_name_and_index);
        normalized_eff_names = (uu___251_19396.normalized_eff_names);
        proof_ns = (uu___251_19396.proof_ns);
        synth_hook = (uu___251_19396.synth_hook);
        splice = (uu___251_19396.splice);
        is_native_tactic = (uu___251_19396.is_native_tactic);
        identifier_info = (uu___251_19396.identifier_info);
        tc_hooks = (uu___251_19396.tc_hooks);
        dsenv = (uu___251_19396.dsenv);
        dep_graph = (uu___251_19396.dep_graph);
        nbe = (uu___251_19396.nbe)
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
            (let uu___252_19451 = env  in
             {
               solver = (uu___252_19451.solver);
               range = (uu___252_19451.range);
               curmodule = (uu___252_19451.curmodule);
               gamma = rest;
               gamma_sig = (uu___252_19451.gamma_sig);
               gamma_cache = (uu___252_19451.gamma_cache);
               modules = (uu___252_19451.modules);
               expected_typ = (uu___252_19451.expected_typ);
               sigtab = (uu___252_19451.sigtab);
               attrtab = (uu___252_19451.attrtab);
               is_pattern = (uu___252_19451.is_pattern);
               instantiate_imp = (uu___252_19451.instantiate_imp);
               effects = (uu___252_19451.effects);
               generalize = (uu___252_19451.generalize);
               letrecs = (uu___252_19451.letrecs);
               top_level = (uu___252_19451.top_level);
               check_uvars = (uu___252_19451.check_uvars);
               use_eq = (uu___252_19451.use_eq);
               is_iface = (uu___252_19451.is_iface);
               admit = (uu___252_19451.admit);
               lax = (uu___252_19451.lax);
               lax_universes = (uu___252_19451.lax_universes);
               phase1 = (uu___252_19451.phase1);
               failhard = (uu___252_19451.failhard);
               nosynth = (uu___252_19451.nosynth);
               uvar_subtyping = (uu___252_19451.uvar_subtyping);
               tc_term = (uu___252_19451.tc_term);
               type_of = (uu___252_19451.type_of);
               universe_of = (uu___252_19451.universe_of);
               check_type_of = (uu___252_19451.check_type_of);
               use_bv_sorts = (uu___252_19451.use_bv_sorts);
               qtbl_name_and_index = (uu___252_19451.qtbl_name_and_index);
               normalized_eff_names = (uu___252_19451.normalized_eff_names);
               proof_ns = (uu___252_19451.proof_ns);
               synth_hook = (uu___252_19451.synth_hook);
               splice = (uu___252_19451.splice);
               is_native_tactic = (uu___252_19451.is_native_tactic);
               identifier_info = (uu___252_19451.identifier_info);
               tc_hooks = (uu___252_19451.tc_hooks);
               dsenv = (uu___252_19451.dsenv);
               dep_graph = (uu___252_19451.dep_graph);
               nbe = (uu___252_19451.nbe)
             }))
    | uu____19452 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19480  ->
             match uu____19480 with | (x,uu____19488) -> push_bv env1 x) env
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
            let uu___253_19522 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___253_19522.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___253_19522.FStar_Syntax_Syntax.index);
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
      (let uu___254_19562 = env  in
       {
         solver = (uu___254_19562.solver);
         range = (uu___254_19562.range);
         curmodule = (uu___254_19562.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___254_19562.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___254_19562.sigtab);
         attrtab = (uu___254_19562.attrtab);
         is_pattern = (uu___254_19562.is_pattern);
         instantiate_imp = (uu___254_19562.instantiate_imp);
         effects = (uu___254_19562.effects);
         generalize = (uu___254_19562.generalize);
         letrecs = (uu___254_19562.letrecs);
         top_level = (uu___254_19562.top_level);
         check_uvars = (uu___254_19562.check_uvars);
         use_eq = (uu___254_19562.use_eq);
         is_iface = (uu___254_19562.is_iface);
         admit = (uu___254_19562.admit);
         lax = (uu___254_19562.lax);
         lax_universes = (uu___254_19562.lax_universes);
         phase1 = (uu___254_19562.phase1);
         failhard = (uu___254_19562.failhard);
         nosynth = (uu___254_19562.nosynth);
         uvar_subtyping = (uu___254_19562.uvar_subtyping);
         tc_term = (uu___254_19562.tc_term);
         type_of = (uu___254_19562.type_of);
         universe_of = (uu___254_19562.universe_of);
         check_type_of = (uu___254_19562.check_type_of);
         use_bv_sorts = (uu___254_19562.use_bv_sorts);
         qtbl_name_and_index = (uu___254_19562.qtbl_name_and_index);
         normalized_eff_names = (uu___254_19562.normalized_eff_names);
         proof_ns = (uu___254_19562.proof_ns);
         synth_hook = (uu___254_19562.synth_hook);
         splice = (uu___254_19562.splice);
         is_native_tactic = (uu___254_19562.is_native_tactic);
         identifier_info = (uu___254_19562.identifier_info);
         tc_hooks = (uu___254_19562.tc_hooks);
         dsenv = (uu___254_19562.dsenv);
         dep_graph = (uu___254_19562.dep_graph);
         nbe = (uu___254_19562.nbe)
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
        let uu____19604 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19604 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19632 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19632)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___255_19647 = env  in
      {
        solver = (uu___255_19647.solver);
        range = (uu___255_19647.range);
        curmodule = (uu___255_19647.curmodule);
        gamma = (uu___255_19647.gamma);
        gamma_sig = (uu___255_19647.gamma_sig);
        gamma_cache = (uu___255_19647.gamma_cache);
        modules = (uu___255_19647.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___255_19647.sigtab);
        attrtab = (uu___255_19647.attrtab);
        is_pattern = (uu___255_19647.is_pattern);
        instantiate_imp = (uu___255_19647.instantiate_imp);
        effects = (uu___255_19647.effects);
        generalize = (uu___255_19647.generalize);
        letrecs = (uu___255_19647.letrecs);
        top_level = (uu___255_19647.top_level);
        check_uvars = (uu___255_19647.check_uvars);
        use_eq = false;
        is_iface = (uu___255_19647.is_iface);
        admit = (uu___255_19647.admit);
        lax = (uu___255_19647.lax);
        lax_universes = (uu___255_19647.lax_universes);
        phase1 = (uu___255_19647.phase1);
        failhard = (uu___255_19647.failhard);
        nosynth = (uu___255_19647.nosynth);
        uvar_subtyping = (uu___255_19647.uvar_subtyping);
        tc_term = (uu___255_19647.tc_term);
        type_of = (uu___255_19647.type_of);
        universe_of = (uu___255_19647.universe_of);
        check_type_of = (uu___255_19647.check_type_of);
        use_bv_sorts = (uu___255_19647.use_bv_sorts);
        qtbl_name_and_index = (uu___255_19647.qtbl_name_and_index);
        normalized_eff_names = (uu___255_19647.normalized_eff_names);
        proof_ns = (uu___255_19647.proof_ns);
        synth_hook = (uu___255_19647.synth_hook);
        splice = (uu___255_19647.splice);
        is_native_tactic = (uu___255_19647.is_native_tactic);
        identifier_info = (uu___255_19647.identifier_info);
        tc_hooks = (uu___255_19647.tc_hooks);
        dsenv = (uu___255_19647.dsenv);
        dep_graph = (uu___255_19647.dep_graph);
        nbe = (uu___255_19647.nbe)
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
    let uu____19675 = expected_typ env_  in
    ((let uu___256_19681 = env_  in
      {
        solver = (uu___256_19681.solver);
        range = (uu___256_19681.range);
        curmodule = (uu___256_19681.curmodule);
        gamma = (uu___256_19681.gamma);
        gamma_sig = (uu___256_19681.gamma_sig);
        gamma_cache = (uu___256_19681.gamma_cache);
        modules = (uu___256_19681.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___256_19681.sigtab);
        attrtab = (uu___256_19681.attrtab);
        is_pattern = (uu___256_19681.is_pattern);
        instantiate_imp = (uu___256_19681.instantiate_imp);
        effects = (uu___256_19681.effects);
        generalize = (uu___256_19681.generalize);
        letrecs = (uu___256_19681.letrecs);
        top_level = (uu___256_19681.top_level);
        check_uvars = (uu___256_19681.check_uvars);
        use_eq = false;
        is_iface = (uu___256_19681.is_iface);
        admit = (uu___256_19681.admit);
        lax = (uu___256_19681.lax);
        lax_universes = (uu___256_19681.lax_universes);
        phase1 = (uu___256_19681.phase1);
        failhard = (uu___256_19681.failhard);
        nosynth = (uu___256_19681.nosynth);
        uvar_subtyping = (uu___256_19681.uvar_subtyping);
        tc_term = (uu___256_19681.tc_term);
        type_of = (uu___256_19681.type_of);
        universe_of = (uu___256_19681.universe_of);
        check_type_of = (uu___256_19681.check_type_of);
        use_bv_sorts = (uu___256_19681.use_bv_sorts);
        qtbl_name_and_index = (uu___256_19681.qtbl_name_and_index);
        normalized_eff_names = (uu___256_19681.normalized_eff_names);
        proof_ns = (uu___256_19681.proof_ns);
        synth_hook = (uu___256_19681.synth_hook);
        splice = (uu___256_19681.splice);
        is_native_tactic = (uu___256_19681.is_native_tactic);
        identifier_info = (uu___256_19681.identifier_info);
        tc_hooks = (uu___256_19681.tc_hooks);
        dsenv = (uu___256_19681.dsenv);
        dep_graph = (uu___256_19681.dep_graph);
        nbe = (uu___256_19681.nbe)
      }), uu____19675)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19691 =
      let uu____19694 = FStar_Ident.id_of_text ""  in [uu____19694]  in
    FStar_Ident.lid_of_ids uu____19691  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19700 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19700
        then
          let uu____19703 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19703 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___257_19730 = env  in
       {
         solver = (uu___257_19730.solver);
         range = (uu___257_19730.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_19730.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___257_19730.expected_typ);
         sigtab = (uu___257_19730.sigtab);
         attrtab = (uu___257_19730.attrtab);
         is_pattern = (uu___257_19730.is_pattern);
         instantiate_imp = (uu___257_19730.instantiate_imp);
         effects = (uu___257_19730.effects);
         generalize = (uu___257_19730.generalize);
         letrecs = (uu___257_19730.letrecs);
         top_level = (uu___257_19730.top_level);
         check_uvars = (uu___257_19730.check_uvars);
         use_eq = (uu___257_19730.use_eq);
         is_iface = (uu___257_19730.is_iface);
         admit = (uu___257_19730.admit);
         lax = (uu___257_19730.lax);
         lax_universes = (uu___257_19730.lax_universes);
         phase1 = (uu___257_19730.phase1);
         failhard = (uu___257_19730.failhard);
         nosynth = (uu___257_19730.nosynth);
         uvar_subtyping = (uu___257_19730.uvar_subtyping);
         tc_term = (uu___257_19730.tc_term);
         type_of = (uu___257_19730.type_of);
         universe_of = (uu___257_19730.universe_of);
         check_type_of = (uu___257_19730.check_type_of);
         use_bv_sorts = (uu___257_19730.use_bv_sorts);
         qtbl_name_and_index = (uu___257_19730.qtbl_name_and_index);
         normalized_eff_names = (uu___257_19730.normalized_eff_names);
         proof_ns = (uu___257_19730.proof_ns);
         synth_hook = (uu___257_19730.synth_hook);
         splice = (uu___257_19730.splice);
         is_native_tactic = (uu___257_19730.is_native_tactic);
         identifier_info = (uu___257_19730.identifier_info);
         tc_hooks = (uu___257_19730.tc_hooks);
         dsenv = (uu___257_19730.dsenv);
         dep_graph = (uu___257_19730.dep_graph);
         nbe = (uu___257_19730.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19781)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19785,(uu____19786,t)))::tl1
          ->
          let uu____19807 =
            let uu____19810 = FStar_Syntax_Free.uvars t  in
            ext out uu____19810  in
          aux uu____19807 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19813;
            FStar_Syntax_Syntax.index = uu____19814;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19821 =
            let uu____19824 = FStar_Syntax_Free.uvars t  in
            ext out uu____19824  in
          aux uu____19821 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19881)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19885,(uu____19886,t)))::tl1
          ->
          let uu____19907 =
            let uu____19910 = FStar_Syntax_Free.univs t  in
            ext out uu____19910  in
          aux uu____19907 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19913;
            FStar_Syntax_Syntax.index = uu____19914;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19921 =
            let uu____19924 = FStar_Syntax_Free.univs t  in
            ext out uu____19924  in
          aux uu____19921 tl1
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
          let uu____19985 = FStar_Util.set_add uname out  in
          aux uu____19985 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19988,(uu____19989,t)))::tl1
          ->
          let uu____20010 =
            let uu____20013 = FStar_Syntax_Free.univnames t  in
            ext out uu____20013  in
          aux uu____20010 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20016;
            FStar_Syntax_Syntax.index = uu____20017;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20024 =
            let uu____20027 = FStar_Syntax_Free.univnames t  in
            ext out uu____20027  in
          aux uu____20024 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___231_20047  ->
            match uu___231_20047 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20051 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20064 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20074 =
      let uu____20083 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20083
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20074 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20127 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___232_20137  ->
              match uu___232_20137 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20139 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20139
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20142) ->
                  let uu____20159 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20159))
       in
    FStar_All.pipe_right uu____20127 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___233_20166  ->
    match uu___233_20166 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20168 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20168
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20188  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20230) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20249,uu____20250) -> false  in
      let uu____20259 =
        FStar_List.tryFind
          (fun uu____20277  ->
             match uu____20277 with | (p,uu____20285) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20259 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20296,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20318 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20318
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___258_20336 = e  in
        {
          solver = (uu___258_20336.solver);
          range = (uu___258_20336.range);
          curmodule = (uu___258_20336.curmodule);
          gamma = (uu___258_20336.gamma);
          gamma_sig = (uu___258_20336.gamma_sig);
          gamma_cache = (uu___258_20336.gamma_cache);
          modules = (uu___258_20336.modules);
          expected_typ = (uu___258_20336.expected_typ);
          sigtab = (uu___258_20336.sigtab);
          attrtab = (uu___258_20336.attrtab);
          is_pattern = (uu___258_20336.is_pattern);
          instantiate_imp = (uu___258_20336.instantiate_imp);
          effects = (uu___258_20336.effects);
          generalize = (uu___258_20336.generalize);
          letrecs = (uu___258_20336.letrecs);
          top_level = (uu___258_20336.top_level);
          check_uvars = (uu___258_20336.check_uvars);
          use_eq = (uu___258_20336.use_eq);
          is_iface = (uu___258_20336.is_iface);
          admit = (uu___258_20336.admit);
          lax = (uu___258_20336.lax);
          lax_universes = (uu___258_20336.lax_universes);
          phase1 = (uu___258_20336.phase1);
          failhard = (uu___258_20336.failhard);
          nosynth = (uu___258_20336.nosynth);
          uvar_subtyping = (uu___258_20336.uvar_subtyping);
          tc_term = (uu___258_20336.tc_term);
          type_of = (uu___258_20336.type_of);
          universe_of = (uu___258_20336.universe_of);
          check_type_of = (uu___258_20336.check_type_of);
          use_bv_sorts = (uu___258_20336.use_bv_sorts);
          qtbl_name_and_index = (uu___258_20336.qtbl_name_and_index);
          normalized_eff_names = (uu___258_20336.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___258_20336.synth_hook);
          splice = (uu___258_20336.splice);
          is_native_tactic = (uu___258_20336.is_native_tactic);
          identifier_info = (uu___258_20336.identifier_info);
          tc_hooks = (uu___258_20336.tc_hooks);
          dsenv = (uu___258_20336.dsenv);
          dep_graph = (uu___258_20336.dep_graph);
          nbe = (uu___258_20336.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___259_20376 = e  in
      {
        solver = (uu___259_20376.solver);
        range = (uu___259_20376.range);
        curmodule = (uu___259_20376.curmodule);
        gamma = (uu___259_20376.gamma);
        gamma_sig = (uu___259_20376.gamma_sig);
        gamma_cache = (uu___259_20376.gamma_cache);
        modules = (uu___259_20376.modules);
        expected_typ = (uu___259_20376.expected_typ);
        sigtab = (uu___259_20376.sigtab);
        attrtab = (uu___259_20376.attrtab);
        is_pattern = (uu___259_20376.is_pattern);
        instantiate_imp = (uu___259_20376.instantiate_imp);
        effects = (uu___259_20376.effects);
        generalize = (uu___259_20376.generalize);
        letrecs = (uu___259_20376.letrecs);
        top_level = (uu___259_20376.top_level);
        check_uvars = (uu___259_20376.check_uvars);
        use_eq = (uu___259_20376.use_eq);
        is_iface = (uu___259_20376.is_iface);
        admit = (uu___259_20376.admit);
        lax = (uu___259_20376.lax);
        lax_universes = (uu___259_20376.lax_universes);
        phase1 = (uu___259_20376.phase1);
        failhard = (uu___259_20376.failhard);
        nosynth = (uu___259_20376.nosynth);
        uvar_subtyping = (uu___259_20376.uvar_subtyping);
        tc_term = (uu___259_20376.tc_term);
        type_of = (uu___259_20376.type_of);
        universe_of = (uu___259_20376.universe_of);
        check_type_of = (uu___259_20376.check_type_of);
        use_bv_sorts = (uu___259_20376.use_bv_sorts);
        qtbl_name_and_index = (uu___259_20376.qtbl_name_and_index);
        normalized_eff_names = (uu___259_20376.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___259_20376.synth_hook);
        splice = (uu___259_20376.splice);
        is_native_tactic = (uu___259_20376.is_native_tactic);
        identifier_info = (uu___259_20376.identifier_info);
        tc_hooks = (uu___259_20376.tc_hooks);
        dsenv = (uu___259_20376.dsenv);
        dep_graph = (uu___259_20376.dep_graph);
        nbe = (uu___259_20376.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20391 = FStar_Syntax_Free.names t  in
      let uu____20394 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20391 uu____20394
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20415 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20415
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20423 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20423
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20440 =
      match uu____20440 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20450 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20450)
       in
    let uu____20452 =
      let uu____20455 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20455 FStar_List.rev  in
    FStar_All.pipe_right uu____20452 (FStar_String.concat " ")
  
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
                  (let uu____20508 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20508 with
                   | FStar_Pervasives_Native.Some uu____20511 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20512 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20518;
        univ_ineqs = uu____20519; implicits = uu____20520;_} -> true
    | uu____20531 -> false
  
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
          let uu___260_20558 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___260_20558.deferred);
            univ_ineqs = (uu___260_20558.univ_ineqs);
            implicits = (uu___260_20558.implicits)
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
          let uu____20593 = FStar_Options.defensive ()  in
          if uu____20593
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20597 =
              let uu____20598 =
                let uu____20599 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20599  in
              Prims.op_Negation uu____20598  in
            (if uu____20597
             then
               let uu____20604 =
                 let uu____20609 =
                   let uu____20610 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20611 =
                     let uu____20612 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20612
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20610 uu____20611
                    in
                 (FStar_Errors.Warning_Defensive, uu____20609)  in
               FStar_Errors.log_issue rng uu____20604
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
          let uu____20643 =
            let uu____20644 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20644  in
          if uu____20643
          then ()
          else
            (let uu____20646 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20646 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20669 =
            let uu____20670 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20670  in
          if uu____20669
          then ()
          else
            (let uu____20672 = bound_vars e  in
             def_check_closed_in rng msg uu____20672 t)
  
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
          let uu___261_20707 = g  in
          let uu____20708 =
            let uu____20709 =
              let uu____20710 =
                let uu____20717 =
                  let uu____20718 =
                    let uu____20735 =
                      let uu____20746 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20746]  in
                    (f, uu____20735)  in
                  FStar_Syntax_Syntax.Tm_app uu____20718  in
                FStar_Syntax_Syntax.mk uu____20717  in
              uu____20710 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20709
             in
          {
            guard_f = uu____20708;
            deferred = (uu___261_20707.deferred);
            univ_ineqs = (uu___261_20707.univ_ineqs);
            implicits = (uu___261_20707.implicits)
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
          let uu___262_20802 = g  in
          let uu____20803 =
            let uu____20804 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20804  in
          {
            guard_f = uu____20803;
            deferred = (uu___262_20802.deferred);
            univ_ineqs = (uu___262_20802.univ_ineqs);
            implicits = (uu___262_20802.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20810 ->
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
          let uu____20825 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____20825
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____20831 =
      let uu____20832 = FStar_Syntax_Util.unmeta t  in
      uu____20832.FStar_Syntax_Syntax.n  in
    match uu____20831 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____20836 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____20877 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____20877;
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
                       let uu____20958 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____20958
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___263_20962 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___263_20962.deferred);
              univ_ineqs = (uu___263_20962.univ_ineqs);
              implicits = (uu___263_20962.implicits)
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
               let uu____20995 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____20995
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
            let uu___264_21018 = g  in
            let uu____21019 =
              let uu____21020 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21020  in
            {
              guard_f = uu____21019;
              deferred = (uu___264_21018.deferred);
              univ_ineqs = (uu___264_21018.univ_ineqs);
              implicits = (uu___264_21018.implicits)
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
            let uu____21058 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21058 with
            | FStar_Pervasives_Native.Some
                (uu____21083::(tm,uu____21085)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21149 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21167 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21167;
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
                    let uu___265_21202 = trivial_guard  in
                    {
                      guard_f = (uu___265_21202.guard_f);
                      deferred = (uu___265_21202.deferred);
                      univ_ineqs = (uu___265_21202.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21219  -> ());
    push = (fun uu____21221  -> ());
    pop = (fun uu____21223  -> ());
    snapshot =
      (fun uu____21225  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21234  -> fun uu____21235  -> ());
    encode_modul = (fun uu____21246  -> fun uu____21247  -> ());
    encode_sig = (fun uu____21250  -> fun uu____21251  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21257 =
             let uu____21264 = FStar_Options.peek ()  in (e, g, uu____21264)
              in
           [uu____21257]);
    solve = (fun uu____21280  -> fun uu____21281  -> fun uu____21282  -> ());
    finish = (fun uu____21288  -> ());
    refresh = (fun uu____21290  -> ())
  } 