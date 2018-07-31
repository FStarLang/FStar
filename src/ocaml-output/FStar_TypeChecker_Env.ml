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
  | UnfoldAttr of FStar_Ident.lid Prims.list 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____37 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____43 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____49 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____69 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____75 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____81 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____87 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____93 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____99 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____106 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____122 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____144 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____166 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____185 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____191 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____197 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____203 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____209 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____215 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____221 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____227 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____233 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____239 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____245 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____251 -> false 
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
      | (Weak ,Weak ) -> true
      | (HNF ,HNF ) -> true
      | (Primops ,Primops ) -> true
      | (Eager_unfolding ,Eager_unfolding ) -> true
      | (Inlining ,Inlining ) -> true
      | (DoNotUnfoldPureLets ,DoNotUnfoldPureLets ) -> true
      | (UnfoldTac ,UnfoldTac ) -> true
      | (PureSubtermsWithinComputations ,PureSubtermsWithinComputations ) ->
          true
      | (Simplify ,Simplify ) -> true
      | (EraseUniverses ,EraseUniverses ) -> true
      | (AllowUnboundUniverses ,AllowUnboundUniverses ) -> true
      | (Reify ,Reify ) -> true
      | (CompressUvars ,CompressUvars ) -> true
      | (NoFullNorm ,NoFullNorm ) -> true
      | (CheckNoUvars ,CheckNoUvars ) -> true
      | (Unmeta ,Unmeta ) -> true
      | (Unascribe ,Unascribe ) -> true
      | (NBE ,NBE ) -> true
      | (Exclude s11,Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11,UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1,UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1,UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr lids1,UnfoldAttr lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | uu____286 -> false
  
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
    match projectee with | NoDelta  -> true | uu____307 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____313 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____319 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____326 -> false
  
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
           (fun uu___223_9865  ->
              match uu___223_9865 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9868 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9868  in
                  let uu____9869 =
                    let uu____9870 = FStar_Syntax_Subst.compress y  in
                    uu____9870.FStar_Syntax_Syntax.n  in
                  (match uu____9869 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9874 =
                         let uu___237_9875 = y1  in
                         let uu____9876 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___237_9875.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___237_9875.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9876
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9874
                   | uu____9879 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___238_9891 = env  in
      let uu____9892 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___238_9891.solver);
        range = (uu___238_9891.range);
        curmodule = (uu___238_9891.curmodule);
        gamma = uu____9892;
        gamma_sig = (uu___238_9891.gamma_sig);
        gamma_cache = (uu___238_9891.gamma_cache);
        modules = (uu___238_9891.modules);
        expected_typ = (uu___238_9891.expected_typ);
        sigtab = (uu___238_9891.sigtab);
        attrtab = (uu___238_9891.attrtab);
        is_pattern = (uu___238_9891.is_pattern);
        instantiate_imp = (uu___238_9891.instantiate_imp);
        effects = (uu___238_9891.effects);
        generalize = (uu___238_9891.generalize);
        letrecs = (uu___238_9891.letrecs);
        top_level = (uu___238_9891.top_level);
        check_uvars = (uu___238_9891.check_uvars);
        use_eq = (uu___238_9891.use_eq);
        is_iface = (uu___238_9891.is_iface);
        admit = (uu___238_9891.admit);
        lax = (uu___238_9891.lax);
        lax_universes = (uu___238_9891.lax_universes);
        phase1 = (uu___238_9891.phase1);
        failhard = (uu___238_9891.failhard);
        nosynth = (uu___238_9891.nosynth);
        uvar_subtyping = (uu___238_9891.uvar_subtyping);
        tc_term = (uu___238_9891.tc_term);
        type_of = (uu___238_9891.type_of);
        universe_of = (uu___238_9891.universe_of);
        check_type_of = (uu___238_9891.check_type_of);
        use_bv_sorts = (uu___238_9891.use_bv_sorts);
        qtbl_name_and_index = (uu___238_9891.qtbl_name_and_index);
        normalized_eff_names = (uu___238_9891.normalized_eff_names);
        proof_ns = (uu___238_9891.proof_ns);
        synth_hook = (uu___238_9891.synth_hook);
        splice = (uu___238_9891.splice);
        is_native_tactic = (uu___238_9891.is_native_tactic);
        identifier_info = (uu___238_9891.identifier_info);
        tc_hooks = (uu___238_9891.tc_hooks);
        dsenv = (uu___238_9891.dsenv);
        dep_graph = (uu___238_9891.dep_graph);
        nbe = (uu___238_9891.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9899  -> fun uu____9900  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___239_9920 = env  in
      {
        solver = (uu___239_9920.solver);
        range = (uu___239_9920.range);
        curmodule = (uu___239_9920.curmodule);
        gamma = (uu___239_9920.gamma);
        gamma_sig = (uu___239_9920.gamma_sig);
        gamma_cache = (uu___239_9920.gamma_cache);
        modules = (uu___239_9920.modules);
        expected_typ = (uu___239_9920.expected_typ);
        sigtab = (uu___239_9920.sigtab);
        attrtab = (uu___239_9920.attrtab);
        is_pattern = (uu___239_9920.is_pattern);
        instantiate_imp = (uu___239_9920.instantiate_imp);
        effects = (uu___239_9920.effects);
        generalize = (uu___239_9920.generalize);
        letrecs = (uu___239_9920.letrecs);
        top_level = (uu___239_9920.top_level);
        check_uvars = (uu___239_9920.check_uvars);
        use_eq = (uu___239_9920.use_eq);
        is_iface = (uu___239_9920.is_iface);
        admit = (uu___239_9920.admit);
        lax = (uu___239_9920.lax);
        lax_universes = (uu___239_9920.lax_universes);
        phase1 = (uu___239_9920.phase1);
        failhard = (uu___239_9920.failhard);
        nosynth = (uu___239_9920.nosynth);
        uvar_subtyping = (uu___239_9920.uvar_subtyping);
        tc_term = (uu___239_9920.tc_term);
        type_of = (uu___239_9920.type_of);
        universe_of = (uu___239_9920.universe_of);
        check_type_of = (uu___239_9920.check_type_of);
        use_bv_sorts = (uu___239_9920.use_bv_sorts);
        qtbl_name_and_index = (uu___239_9920.qtbl_name_and_index);
        normalized_eff_names = (uu___239_9920.normalized_eff_names);
        proof_ns = (uu___239_9920.proof_ns);
        synth_hook = (uu___239_9920.synth_hook);
        splice = (uu___239_9920.splice);
        is_native_tactic = (uu___239_9920.is_native_tactic);
        identifier_info = (uu___239_9920.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___239_9920.dsenv);
        dep_graph = (uu___239_9920.dep_graph);
        nbe = (uu___239_9920.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___240_9931 = e  in
      {
        solver = (uu___240_9931.solver);
        range = (uu___240_9931.range);
        curmodule = (uu___240_9931.curmodule);
        gamma = (uu___240_9931.gamma);
        gamma_sig = (uu___240_9931.gamma_sig);
        gamma_cache = (uu___240_9931.gamma_cache);
        modules = (uu___240_9931.modules);
        expected_typ = (uu___240_9931.expected_typ);
        sigtab = (uu___240_9931.sigtab);
        attrtab = (uu___240_9931.attrtab);
        is_pattern = (uu___240_9931.is_pattern);
        instantiate_imp = (uu___240_9931.instantiate_imp);
        effects = (uu___240_9931.effects);
        generalize = (uu___240_9931.generalize);
        letrecs = (uu___240_9931.letrecs);
        top_level = (uu___240_9931.top_level);
        check_uvars = (uu___240_9931.check_uvars);
        use_eq = (uu___240_9931.use_eq);
        is_iface = (uu___240_9931.is_iface);
        admit = (uu___240_9931.admit);
        lax = (uu___240_9931.lax);
        lax_universes = (uu___240_9931.lax_universes);
        phase1 = (uu___240_9931.phase1);
        failhard = (uu___240_9931.failhard);
        nosynth = (uu___240_9931.nosynth);
        uvar_subtyping = (uu___240_9931.uvar_subtyping);
        tc_term = (uu___240_9931.tc_term);
        type_of = (uu___240_9931.type_of);
        universe_of = (uu___240_9931.universe_of);
        check_type_of = (uu___240_9931.check_type_of);
        use_bv_sorts = (uu___240_9931.use_bv_sorts);
        qtbl_name_and_index = (uu___240_9931.qtbl_name_and_index);
        normalized_eff_names = (uu___240_9931.normalized_eff_names);
        proof_ns = (uu___240_9931.proof_ns);
        synth_hook = (uu___240_9931.synth_hook);
        splice = (uu___240_9931.splice);
        is_native_tactic = (uu___240_9931.is_native_tactic);
        identifier_info = (uu___240_9931.identifier_info);
        tc_hooks = (uu___240_9931.tc_hooks);
        dsenv = (uu___240_9931.dsenv);
        dep_graph = g;
        nbe = (uu___240_9931.nbe)
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
      | (NoDelta ,uu____9954) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____9955,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____9956,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____9957 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____9966 . unit -> 'Auu____9966 FStar_Util.smap =
  fun uu____9973  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____9978 . unit -> 'Auu____9978 FStar_Util.smap =
  fun uu____9985  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____10119 = new_gamma_cache ()  in
                  let uu____10122 = new_sigtab ()  in
                  let uu____10125 = new_sigtab ()  in
                  let uu____10132 =
                    let uu____10145 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____10145, FStar_Pervasives_Native.None)  in
                  let uu____10160 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____10163 = FStar_Options.using_facts_from ()  in
                  let uu____10164 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____10167 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10119;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10122;
                    attrtab = uu____10125;
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
                    qtbl_name_and_index = uu____10132;
                    normalized_eff_names = uu____10160;
                    proof_ns = uu____10163;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10203  -> false);
                    identifier_info = uu____10164;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10167;
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
  fun uu____10303  ->
    let uu____10304 = FStar_ST.op_Bang query_indices  in
    match uu____10304 with
    | [] -> failwith "Empty query indices!"
    | uu____10354 ->
        let uu____10363 =
          let uu____10372 =
            let uu____10379 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10379  in
          let uu____10429 = FStar_ST.op_Bang query_indices  in uu____10372 ::
            uu____10429
           in
        FStar_ST.op_Colon_Equals query_indices uu____10363
  
let (pop_query_indices : unit -> unit) =
  fun uu____10518  ->
    let uu____10519 = FStar_ST.op_Bang query_indices  in
    match uu____10519 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10634  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10664  ->
    match uu____10664 with
    | (l,n1) ->
        let uu____10671 = FStar_ST.op_Bang query_indices  in
        (match uu____10671 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10782 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10801  ->
    let uu____10802 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10802
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10875 =
       let uu____10878 = FStar_ST.op_Bang stack  in env :: uu____10878  in
     FStar_ST.op_Colon_Equals stack uu____10875);
    (let uu___241_10927 = env  in
     let uu____10928 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____10931 = FStar_Util.smap_copy (sigtab env)  in
     let uu____10934 = FStar_Util.smap_copy (attrtab env)  in
     let uu____10941 =
       let uu____10954 =
         let uu____10957 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____10957  in
       let uu____10982 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____10954, uu____10982)  in
     let uu____11023 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____11026 =
       let uu____11029 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____11029  in
     {
       solver = (uu___241_10927.solver);
       range = (uu___241_10927.range);
       curmodule = (uu___241_10927.curmodule);
       gamma = (uu___241_10927.gamma);
       gamma_sig = (uu___241_10927.gamma_sig);
       gamma_cache = uu____10928;
       modules = (uu___241_10927.modules);
       expected_typ = (uu___241_10927.expected_typ);
       sigtab = uu____10931;
       attrtab = uu____10934;
       is_pattern = (uu___241_10927.is_pattern);
       instantiate_imp = (uu___241_10927.instantiate_imp);
       effects = (uu___241_10927.effects);
       generalize = (uu___241_10927.generalize);
       letrecs = (uu___241_10927.letrecs);
       top_level = (uu___241_10927.top_level);
       check_uvars = (uu___241_10927.check_uvars);
       use_eq = (uu___241_10927.use_eq);
       is_iface = (uu___241_10927.is_iface);
       admit = (uu___241_10927.admit);
       lax = (uu___241_10927.lax);
       lax_universes = (uu___241_10927.lax_universes);
       phase1 = (uu___241_10927.phase1);
       failhard = (uu___241_10927.failhard);
       nosynth = (uu___241_10927.nosynth);
       uvar_subtyping = (uu___241_10927.uvar_subtyping);
       tc_term = (uu___241_10927.tc_term);
       type_of = (uu___241_10927.type_of);
       universe_of = (uu___241_10927.universe_of);
       check_type_of = (uu___241_10927.check_type_of);
       use_bv_sorts = (uu___241_10927.use_bv_sorts);
       qtbl_name_and_index = uu____10941;
       normalized_eff_names = uu____11023;
       proof_ns = (uu___241_10927.proof_ns);
       synth_hook = (uu___241_10927.synth_hook);
       splice = (uu___241_10927.splice);
       is_native_tactic = (uu___241_10927.is_native_tactic);
       identifier_info = uu____11026;
       tc_hooks = (uu___241_10927.tc_hooks);
       dsenv = (uu___241_10927.dsenv);
       dep_graph = (uu___241_10927.dep_graph);
       nbe = (uu___241_10927.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11075  ->
    let uu____11076 = FStar_ST.op_Bang stack  in
    match uu____11076 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11130 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____11202  ->
           let uu____11203 = snapshot_stack env  in
           match uu____11203 with
           | (stack_depth,env1) ->
               let uu____11228 = snapshot_query_indices ()  in
               (match uu____11228 with
                | (query_indices_depth,()) ->
                    let uu____11252 = (env1.solver).snapshot msg  in
                    (match uu____11252 with
                     | (solver_depth,()) ->
                         let uu____11294 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11294 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___242_11340 = env1  in
                                 {
                                   solver = (uu___242_11340.solver);
                                   range = (uu___242_11340.range);
                                   curmodule = (uu___242_11340.curmodule);
                                   gamma = (uu___242_11340.gamma);
                                   gamma_sig = (uu___242_11340.gamma_sig);
                                   gamma_cache = (uu___242_11340.gamma_cache);
                                   modules = (uu___242_11340.modules);
                                   expected_typ =
                                     (uu___242_11340.expected_typ);
                                   sigtab = (uu___242_11340.sigtab);
                                   attrtab = (uu___242_11340.attrtab);
                                   is_pattern = (uu___242_11340.is_pattern);
                                   instantiate_imp =
                                     (uu___242_11340.instantiate_imp);
                                   effects = (uu___242_11340.effects);
                                   generalize = (uu___242_11340.generalize);
                                   letrecs = (uu___242_11340.letrecs);
                                   top_level = (uu___242_11340.top_level);
                                   check_uvars = (uu___242_11340.check_uvars);
                                   use_eq = (uu___242_11340.use_eq);
                                   is_iface = (uu___242_11340.is_iface);
                                   admit = (uu___242_11340.admit);
                                   lax = (uu___242_11340.lax);
                                   lax_universes =
                                     (uu___242_11340.lax_universes);
                                   phase1 = (uu___242_11340.phase1);
                                   failhard = (uu___242_11340.failhard);
                                   nosynth = (uu___242_11340.nosynth);
                                   uvar_subtyping =
                                     (uu___242_11340.uvar_subtyping);
                                   tc_term = (uu___242_11340.tc_term);
                                   type_of = (uu___242_11340.type_of);
                                   universe_of = (uu___242_11340.universe_of);
                                   check_type_of =
                                     (uu___242_11340.check_type_of);
                                   use_bv_sorts =
                                     (uu___242_11340.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___242_11340.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___242_11340.normalized_eff_names);
                                   proof_ns = (uu___242_11340.proof_ns);
                                   synth_hook = (uu___242_11340.synth_hook);
                                   splice = (uu___242_11340.splice);
                                   is_native_tactic =
                                     (uu___242_11340.is_native_tactic);
                                   identifier_info =
                                     (uu___242_11340.identifier_info);
                                   tc_hooks = (uu___242_11340.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___242_11340.dep_graph);
                                   nbe = (uu___242_11340.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11371  ->
             let uu____11372 =
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
             match uu____11372 with
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
                             ((let uu____11498 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11498
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11509 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11509
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11536,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11568 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11594  ->
                  match uu____11594 with
                  | (m,uu____11600) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11568 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___243_11608 = env  in
               {
                 solver = (uu___243_11608.solver);
                 range = (uu___243_11608.range);
                 curmodule = (uu___243_11608.curmodule);
                 gamma = (uu___243_11608.gamma);
                 gamma_sig = (uu___243_11608.gamma_sig);
                 gamma_cache = (uu___243_11608.gamma_cache);
                 modules = (uu___243_11608.modules);
                 expected_typ = (uu___243_11608.expected_typ);
                 sigtab = (uu___243_11608.sigtab);
                 attrtab = (uu___243_11608.attrtab);
                 is_pattern = (uu___243_11608.is_pattern);
                 instantiate_imp = (uu___243_11608.instantiate_imp);
                 effects = (uu___243_11608.effects);
                 generalize = (uu___243_11608.generalize);
                 letrecs = (uu___243_11608.letrecs);
                 top_level = (uu___243_11608.top_level);
                 check_uvars = (uu___243_11608.check_uvars);
                 use_eq = (uu___243_11608.use_eq);
                 is_iface = (uu___243_11608.is_iface);
                 admit = (uu___243_11608.admit);
                 lax = (uu___243_11608.lax);
                 lax_universes = (uu___243_11608.lax_universes);
                 phase1 = (uu___243_11608.phase1);
                 failhard = (uu___243_11608.failhard);
                 nosynth = (uu___243_11608.nosynth);
                 uvar_subtyping = (uu___243_11608.uvar_subtyping);
                 tc_term = (uu___243_11608.tc_term);
                 type_of = (uu___243_11608.type_of);
                 universe_of = (uu___243_11608.universe_of);
                 check_type_of = (uu___243_11608.check_type_of);
                 use_bv_sorts = (uu___243_11608.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___243_11608.normalized_eff_names);
                 proof_ns = (uu___243_11608.proof_ns);
                 synth_hook = (uu___243_11608.synth_hook);
                 splice = (uu___243_11608.splice);
                 is_native_tactic = (uu___243_11608.is_native_tactic);
                 identifier_info = (uu___243_11608.identifier_info);
                 tc_hooks = (uu___243_11608.tc_hooks);
                 dsenv = (uu___243_11608.dsenv);
                 dep_graph = (uu___243_11608.dep_graph);
                 nbe = (uu___243_11608.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11621,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___244_11630 = env  in
               {
                 solver = (uu___244_11630.solver);
                 range = (uu___244_11630.range);
                 curmodule = (uu___244_11630.curmodule);
                 gamma = (uu___244_11630.gamma);
                 gamma_sig = (uu___244_11630.gamma_sig);
                 gamma_cache = (uu___244_11630.gamma_cache);
                 modules = (uu___244_11630.modules);
                 expected_typ = (uu___244_11630.expected_typ);
                 sigtab = (uu___244_11630.sigtab);
                 attrtab = (uu___244_11630.attrtab);
                 is_pattern = (uu___244_11630.is_pattern);
                 instantiate_imp = (uu___244_11630.instantiate_imp);
                 effects = (uu___244_11630.effects);
                 generalize = (uu___244_11630.generalize);
                 letrecs = (uu___244_11630.letrecs);
                 top_level = (uu___244_11630.top_level);
                 check_uvars = (uu___244_11630.check_uvars);
                 use_eq = (uu___244_11630.use_eq);
                 is_iface = (uu___244_11630.is_iface);
                 admit = (uu___244_11630.admit);
                 lax = (uu___244_11630.lax);
                 lax_universes = (uu___244_11630.lax_universes);
                 phase1 = (uu___244_11630.phase1);
                 failhard = (uu___244_11630.failhard);
                 nosynth = (uu___244_11630.nosynth);
                 uvar_subtyping = (uu___244_11630.uvar_subtyping);
                 tc_term = (uu___244_11630.tc_term);
                 type_of = (uu___244_11630.type_of);
                 universe_of = (uu___244_11630.universe_of);
                 check_type_of = (uu___244_11630.check_type_of);
                 use_bv_sorts = (uu___244_11630.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___244_11630.normalized_eff_names);
                 proof_ns = (uu___244_11630.proof_ns);
                 synth_hook = (uu___244_11630.synth_hook);
                 splice = (uu___244_11630.splice);
                 is_native_tactic = (uu___244_11630.is_native_tactic);
                 identifier_info = (uu___244_11630.identifier_info);
                 tc_hooks = (uu___244_11630.tc_hooks);
                 dsenv = (uu___244_11630.dsenv);
                 dep_graph = (uu___244_11630.dep_graph);
                 nbe = (uu___244_11630.nbe)
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
        (let uu___245_11664 = e  in
         {
           solver = (uu___245_11664.solver);
           range = r;
           curmodule = (uu___245_11664.curmodule);
           gamma = (uu___245_11664.gamma);
           gamma_sig = (uu___245_11664.gamma_sig);
           gamma_cache = (uu___245_11664.gamma_cache);
           modules = (uu___245_11664.modules);
           expected_typ = (uu___245_11664.expected_typ);
           sigtab = (uu___245_11664.sigtab);
           attrtab = (uu___245_11664.attrtab);
           is_pattern = (uu___245_11664.is_pattern);
           instantiate_imp = (uu___245_11664.instantiate_imp);
           effects = (uu___245_11664.effects);
           generalize = (uu___245_11664.generalize);
           letrecs = (uu___245_11664.letrecs);
           top_level = (uu___245_11664.top_level);
           check_uvars = (uu___245_11664.check_uvars);
           use_eq = (uu___245_11664.use_eq);
           is_iface = (uu___245_11664.is_iface);
           admit = (uu___245_11664.admit);
           lax = (uu___245_11664.lax);
           lax_universes = (uu___245_11664.lax_universes);
           phase1 = (uu___245_11664.phase1);
           failhard = (uu___245_11664.failhard);
           nosynth = (uu___245_11664.nosynth);
           uvar_subtyping = (uu___245_11664.uvar_subtyping);
           tc_term = (uu___245_11664.tc_term);
           type_of = (uu___245_11664.type_of);
           universe_of = (uu___245_11664.universe_of);
           check_type_of = (uu___245_11664.check_type_of);
           use_bv_sorts = (uu___245_11664.use_bv_sorts);
           qtbl_name_and_index = (uu___245_11664.qtbl_name_and_index);
           normalized_eff_names = (uu___245_11664.normalized_eff_names);
           proof_ns = (uu___245_11664.proof_ns);
           synth_hook = (uu___245_11664.synth_hook);
           splice = (uu___245_11664.splice);
           is_native_tactic = (uu___245_11664.is_native_tactic);
           identifier_info = (uu___245_11664.identifier_info);
           tc_hooks = (uu___245_11664.tc_hooks);
           dsenv = (uu___245_11664.dsenv);
           dep_graph = (uu___245_11664.dep_graph);
           nbe = (uu___245_11664.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11680 =
        let uu____11681 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11681 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11680
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11735 =
          let uu____11736 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11736 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11735
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11790 =
          let uu____11791 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11791 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11790
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11845 =
        let uu____11846 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11846 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11845
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___246_11907 = env  in
      {
        solver = (uu___246_11907.solver);
        range = (uu___246_11907.range);
        curmodule = lid;
        gamma = (uu___246_11907.gamma);
        gamma_sig = (uu___246_11907.gamma_sig);
        gamma_cache = (uu___246_11907.gamma_cache);
        modules = (uu___246_11907.modules);
        expected_typ = (uu___246_11907.expected_typ);
        sigtab = (uu___246_11907.sigtab);
        attrtab = (uu___246_11907.attrtab);
        is_pattern = (uu___246_11907.is_pattern);
        instantiate_imp = (uu___246_11907.instantiate_imp);
        effects = (uu___246_11907.effects);
        generalize = (uu___246_11907.generalize);
        letrecs = (uu___246_11907.letrecs);
        top_level = (uu___246_11907.top_level);
        check_uvars = (uu___246_11907.check_uvars);
        use_eq = (uu___246_11907.use_eq);
        is_iface = (uu___246_11907.is_iface);
        admit = (uu___246_11907.admit);
        lax = (uu___246_11907.lax);
        lax_universes = (uu___246_11907.lax_universes);
        phase1 = (uu___246_11907.phase1);
        failhard = (uu___246_11907.failhard);
        nosynth = (uu___246_11907.nosynth);
        uvar_subtyping = (uu___246_11907.uvar_subtyping);
        tc_term = (uu___246_11907.tc_term);
        type_of = (uu___246_11907.type_of);
        universe_of = (uu___246_11907.universe_of);
        check_type_of = (uu___246_11907.check_type_of);
        use_bv_sorts = (uu___246_11907.use_bv_sorts);
        qtbl_name_and_index = (uu___246_11907.qtbl_name_and_index);
        normalized_eff_names = (uu___246_11907.normalized_eff_names);
        proof_ns = (uu___246_11907.proof_ns);
        synth_hook = (uu___246_11907.synth_hook);
        splice = (uu___246_11907.splice);
        is_native_tactic = (uu___246_11907.is_native_tactic);
        identifier_info = (uu___246_11907.identifier_info);
        tc_hooks = (uu___246_11907.tc_hooks);
        dsenv = (uu___246_11907.dsenv);
        dep_graph = (uu___246_11907.dep_graph);
        nbe = (uu___246_11907.nbe)
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
      let uu____11934 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11934
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11944 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11944)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11954 =
      let uu____11955 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11955  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11954)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11960  ->
    let uu____11961 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11961
  
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
      | ((formals,t),uu____12055) ->
          let vs = mk_univ_subst formals us  in
          let uu____12079 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12079)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___224_12095  ->
    match uu___224_12095 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12121  -> new_u_univ ()))
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
      let uu____12140 = inst_tscheme t  in
      match uu____12140 with
      | (us,t1) ->
          let uu____12151 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12151)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12171  ->
          match uu____12171 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12192 =
                         let uu____12193 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12194 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12195 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12196 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12193 uu____12194 uu____12195 uu____12196
                          in
                       failwith uu____12192)
                    else ();
                    (let uu____12198 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12198))
               | uu____12207 ->
                   let uu____12208 =
                     let uu____12209 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12209
                      in
                   failwith uu____12208)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12215 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12221 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12227 -> false
  
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
             | ([],uu____12269) -> Maybe
             | (uu____12276,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12295 -> No  in
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
          let uu____12386 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12386 with
          | FStar_Pervasives_Native.None  ->
              let uu____12409 =
                FStar_Util.find_map env.gamma
                  (fun uu___225_12453  ->
                     match uu___225_12453 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12492 = FStar_Ident.lid_equals lid l  in
                         if uu____12492
                         then
                           let uu____12513 =
                             let uu____12532 =
                               let uu____12547 = inst_tscheme t  in
                               FStar_Util.Inl uu____12547  in
                             let uu____12562 = FStar_Ident.range_of_lid l  in
                             (uu____12532, uu____12562)  in
                           FStar_Pervasives_Native.Some uu____12513
                         else FStar_Pervasives_Native.None
                     | uu____12614 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12409
                (fun uu____12652  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___226_12661  ->
                        match uu___226_12661 with
                        | (uu____12664,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12666);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12667;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12668;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12669;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12670;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12690 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12690
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
                                  uu____12738 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12745 -> cache t  in
                            let uu____12746 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12746 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12752 =
                                   let uu____12753 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12753)
                                    in
                                 maybe_cache uu____12752)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12821 = find_in_sigtab env lid  in
         match uu____12821 with
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
      let uu____12901 = lookup_qname env lid  in
      match uu____12901 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12922,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13033 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13033 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13075 =
          let uu____13078 = lookup_attr env1 attr  in se1 :: uu____13078  in
        FStar_Util.smap_add (attrtab env1) attr uu____13075  in
      FStar_List.iter
        (fun attr  ->
           let uu____13088 =
             let uu____13089 = FStar_Syntax_Subst.compress attr  in
             uu____13089.FStar_Syntax_Syntax.n  in
           match uu____13088 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13093 =
                 let uu____13094 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13094.FStar_Ident.str  in
               add_one1 env se uu____13093
           | uu____13095 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13117) ->
          add_sigelts env ses
      | uu____13126 ->
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
            | uu____13141 -> ()))

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
        (fun uu___227_13172  ->
           match uu___227_13172 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13190 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13251,lb::[]),uu____13253) ->
            let uu____13260 =
              let uu____13269 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13278 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13269, uu____13278)  in
            FStar_Pervasives_Native.Some uu____13260
        | FStar_Syntax_Syntax.Sig_let ((uu____13291,lbs),uu____13293) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13323 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13335 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13335
                     then
                       let uu____13346 =
                         let uu____13355 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13364 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13355, uu____13364)  in
                       FStar_Pervasives_Native.Some uu____13346
                     else FStar_Pervasives_Native.None)
        | uu____13386 -> FStar_Pervasives_Native.None
  
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
          let uu____13445 =
            let uu____13454 =
              let uu____13459 =
                let uu____13460 =
                  let uu____13463 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13463
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13460)  in
              inst_tscheme1 uu____13459  in
            (uu____13454, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13445
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13485,uu____13486) ->
          let uu____13491 =
            let uu____13500 =
              let uu____13505 =
                let uu____13506 =
                  let uu____13509 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13509  in
                (us, uu____13506)  in
              inst_tscheme1 uu____13505  in
            (uu____13500, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13491
      | uu____13528 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13616 =
          match uu____13616 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13712,uvs,t,uu____13715,uu____13716,uu____13717);
                      FStar_Syntax_Syntax.sigrng = uu____13718;
                      FStar_Syntax_Syntax.sigquals = uu____13719;
                      FStar_Syntax_Syntax.sigmeta = uu____13720;
                      FStar_Syntax_Syntax.sigattrs = uu____13721;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13742 =
                     let uu____13751 = inst_tscheme1 (uvs, t)  in
                     (uu____13751, rng)  in
                   FStar_Pervasives_Native.Some uu____13742
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13775;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13777;
                      FStar_Syntax_Syntax.sigattrs = uu____13778;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13795 =
                     let uu____13796 = in_cur_mod env l  in uu____13796 = Yes
                      in
                   if uu____13795
                   then
                     let uu____13807 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13807
                      then
                        let uu____13820 =
                          let uu____13829 = inst_tscheme1 (uvs, t)  in
                          (uu____13829, rng)  in
                        FStar_Pervasives_Native.Some uu____13820
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13860 =
                        let uu____13869 = inst_tscheme1 (uvs, t)  in
                        (uu____13869, rng)  in
                      FStar_Pervasives_Native.Some uu____13860)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13894,uu____13895);
                      FStar_Syntax_Syntax.sigrng = uu____13896;
                      FStar_Syntax_Syntax.sigquals = uu____13897;
                      FStar_Syntax_Syntax.sigmeta = uu____13898;
                      FStar_Syntax_Syntax.sigattrs = uu____13899;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13940 =
                          let uu____13949 = inst_tscheme1 (uvs, k)  in
                          (uu____13949, rng)  in
                        FStar_Pervasives_Native.Some uu____13940
                    | uu____13970 ->
                        let uu____13971 =
                          let uu____13980 =
                            let uu____13985 =
                              let uu____13986 =
                                let uu____13989 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13989
                                 in
                              (uvs, uu____13986)  in
                            inst_tscheme1 uu____13985  in
                          (uu____13980, rng)  in
                        FStar_Pervasives_Native.Some uu____13971)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14012,uu____14013);
                      FStar_Syntax_Syntax.sigrng = uu____14014;
                      FStar_Syntax_Syntax.sigquals = uu____14015;
                      FStar_Syntax_Syntax.sigmeta = uu____14016;
                      FStar_Syntax_Syntax.sigattrs = uu____14017;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14059 =
                          let uu____14068 = inst_tscheme_with (uvs, k) us  in
                          (uu____14068, rng)  in
                        FStar_Pervasives_Native.Some uu____14059
                    | uu____14089 ->
                        let uu____14090 =
                          let uu____14099 =
                            let uu____14104 =
                              let uu____14105 =
                                let uu____14108 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14108
                                 in
                              (uvs, uu____14105)  in
                            inst_tscheme_with uu____14104 us  in
                          (uu____14099, rng)  in
                        FStar_Pervasives_Native.Some uu____14090)
               | FStar_Util.Inr se ->
                   let uu____14144 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14165;
                          FStar_Syntax_Syntax.sigrng = uu____14166;
                          FStar_Syntax_Syntax.sigquals = uu____14167;
                          FStar_Syntax_Syntax.sigmeta = uu____14168;
                          FStar_Syntax_Syntax.sigattrs = uu____14169;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14184 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14144
                     (FStar_Util.map_option
                        (fun uu____14232  ->
                           match uu____14232 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14263 =
          let uu____14274 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14274 mapper  in
        match uu____14263 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14348 =
              let uu____14359 =
                let uu____14366 =
                  let uu___247_14369 = t  in
                  let uu____14370 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___247_14369.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14370;
                    FStar_Syntax_Syntax.vars =
                      (uu___247_14369.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14366)  in
              (uu____14359, r)  in
            FStar_Pervasives_Native.Some uu____14348
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14417 = lookup_qname env l  in
      match uu____14417 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14436 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14488 = try_lookup_bv env bv  in
      match uu____14488 with
      | FStar_Pervasives_Native.None  ->
          let uu____14503 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14503 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14518 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14519 =
            let uu____14520 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14520  in
          (uu____14518, uu____14519)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14541 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14541 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14607 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14607  in
          let uu____14608 =
            let uu____14617 =
              let uu____14622 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14622)  in
            (uu____14617, r1)  in
          FStar_Pervasives_Native.Some uu____14608
  
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
        let uu____14656 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14656 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14689,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14714 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14714  in
            let uu____14715 =
              let uu____14720 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14720, r1)  in
            FStar_Pervasives_Native.Some uu____14715
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14743 = try_lookup_lid env l  in
      match uu____14743 with
      | FStar_Pervasives_Native.None  ->
          let uu____14770 = name_not_found l  in
          let uu____14775 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14770 uu____14775
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___228_14815  ->
              match uu___228_14815 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14817 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14836 = lookup_qname env lid  in
      match uu____14836 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14845,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14848;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14850;
              FStar_Syntax_Syntax.sigattrs = uu____14851;_},FStar_Pervasives_Native.None
            ),uu____14852)
          ->
          let uu____14901 =
            let uu____14908 =
              let uu____14909 =
                let uu____14912 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14912 t  in
              (uvs, uu____14909)  in
            (uu____14908, q)  in
          FStar_Pervasives_Native.Some uu____14901
      | uu____14925 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14946 = lookup_qname env lid  in
      match uu____14946 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14951,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14954;
              FStar_Syntax_Syntax.sigquals = uu____14955;
              FStar_Syntax_Syntax.sigmeta = uu____14956;
              FStar_Syntax_Syntax.sigattrs = uu____14957;_},FStar_Pervasives_Native.None
            ),uu____14958)
          ->
          let uu____15007 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15007 (uvs, t)
      | uu____15012 ->
          let uu____15013 = name_not_found lid  in
          let uu____15018 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15013 uu____15018
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15037 = lookup_qname env lid  in
      match uu____15037 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15042,uvs,t,uu____15045,uu____15046,uu____15047);
              FStar_Syntax_Syntax.sigrng = uu____15048;
              FStar_Syntax_Syntax.sigquals = uu____15049;
              FStar_Syntax_Syntax.sigmeta = uu____15050;
              FStar_Syntax_Syntax.sigattrs = uu____15051;_},FStar_Pervasives_Native.None
            ),uu____15052)
          ->
          let uu____15105 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15105 (uvs, t)
      | uu____15110 ->
          let uu____15111 = name_not_found lid  in
          let uu____15116 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15111 uu____15116
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15137 = lookup_qname env lid  in
      match uu____15137 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15144,uu____15145,uu____15146,uu____15147,uu____15148,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15150;
              FStar_Syntax_Syntax.sigquals = uu____15151;
              FStar_Syntax_Syntax.sigmeta = uu____15152;
              FStar_Syntax_Syntax.sigattrs = uu____15153;_},uu____15154),uu____15155)
          -> (true, dcs)
      | uu____15216 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15229 = lookup_qname env lid  in
      match uu____15229 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15230,uu____15231,uu____15232,l,uu____15234,uu____15235);
              FStar_Syntax_Syntax.sigrng = uu____15236;
              FStar_Syntax_Syntax.sigquals = uu____15237;
              FStar_Syntax_Syntax.sigmeta = uu____15238;
              FStar_Syntax_Syntax.sigattrs = uu____15239;_},uu____15240),uu____15241)
          -> l
      | uu____15296 ->
          let uu____15297 =
            let uu____15298 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15298  in
          failwith uu____15297
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15347)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15398,lbs),uu____15400)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15422 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15422
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15454 -> FStar_Pervasives_Native.None)
        | uu____15459 -> FStar_Pervasives_Native.None
  
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
        let uu____15489 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15489
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15514),uu____15515) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15564 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15585),uu____15586) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15635 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15656 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15656
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15675 = lookup_qname env ftv  in
      match uu____15675 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15679) ->
          let uu____15724 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15724 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15745,t),r) ->
               let uu____15760 =
                 let uu____15761 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15761 t  in
               FStar_Pervasives_Native.Some uu____15760)
      | uu____15762 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15773 = try_lookup_effect_lid env ftv  in
      match uu____15773 with
      | FStar_Pervasives_Native.None  ->
          let uu____15776 = name_not_found ftv  in
          let uu____15781 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15776 uu____15781
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
        let uu____15804 = lookup_qname env lid0  in
        match uu____15804 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15815);
                FStar_Syntax_Syntax.sigrng = uu____15816;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15818;
                FStar_Syntax_Syntax.sigattrs = uu____15819;_},FStar_Pervasives_Native.None
              ),uu____15820)
            ->
            let lid1 =
              let uu____15874 =
                let uu____15875 = FStar_Ident.range_of_lid lid  in
                let uu____15876 =
                  let uu____15877 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____15877  in
                FStar_Range.set_use_range uu____15875 uu____15876  in
              FStar_Ident.set_lid_range lid uu____15874  in
            let uu____15878 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___229_15882  ->
                      match uu___229_15882 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____15883 -> false))
               in
            if uu____15878
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15897 =
                      let uu____15898 =
                        let uu____15899 = get_range env  in
                        FStar_Range.string_of_range uu____15899  in
                      let uu____15900 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____15901 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15898 uu____15900 uu____15901
                       in
                    failwith uu____15897)
                  in
               match (binders, univs1) with
               | ([],uu____15918) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____15943,uu____15944::uu____15945::uu____15946) ->
                   let uu____15967 =
                     let uu____15968 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____15969 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____15968 uu____15969
                      in
                   failwith uu____15967
               | uu____15976 ->
                   let uu____15991 =
                     let uu____15996 =
                       let uu____15997 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____15997)  in
                     inst_tscheme_with uu____15996 insts  in
                   (match uu____15991 with
                    | (uu____16010,t) ->
                        let t1 =
                          let uu____16013 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16013 t  in
                        let uu____16014 =
                          let uu____16015 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16015.FStar_Syntax_Syntax.n  in
                        (match uu____16014 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16050 -> failwith "Impossible")))
        | uu____16057 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16080 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16080 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16093,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16100 = find1 l2  in
            (match uu____16100 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16107 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16107 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16111 = find1 l  in
            (match uu____16111 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16116 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16116
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16130 = lookup_qname env l1  in
      match uu____16130 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16133;
              FStar_Syntax_Syntax.sigrng = uu____16134;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16136;
              FStar_Syntax_Syntax.sigattrs = uu____16137;_},uu____16138),uu____16139)
          -> q
      | uu____16190 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16211 =
          let uu____16212 =
            let uu____16213 = FStar_Util.string_of_int i  in
            let uu____16214 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16213 uu____16214
             in
          failwith uu____16212  in
        let uu____16215 = lookup_datacon env lid  in
        match uu____16215 with
        | (uu____16220,t) ->
            let uu____16222 =
              let uu____16223 = FStar_Syntax_Subst.compress t  in
              uu____16223.FStar_Syntax_Syntax.n  in
            (match uu____16222 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16227) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16268 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16268
                      FStar_Pervasives_Native.fst)
             | uu____16279 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16290 = lookup_qname env l  in
      match uu____16290 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16291,uu____16292,uu____16293);
              FStar_Syntax_Syntax.sigrng = uu____16294;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16296;
              FStar_Syntax_Syntax.sigattrs = uu____16297;_},uu____16298),uu____16299)
          ->
          FStar_Util.for_some
            (fun uu___230_16352  ->
               match uu___230_16352 with
               | FStar_Syntax_Syntax.Projector uu____16353 -> true
               | uu____16358 -> false) quals
      | uu____16359 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16370 = lookup_qname env lid  in
      match uu____16370 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16371,uu____16372,uu____16373,uu____16374,uu____16375,uu____16376);
              FStar_Syntax_Syntax.sigrng = uu____16377;
              FStar_Syntax_Syntax.sigquals = uu____16378;
              FStar_Syntax_Syntax.sigmeta = uu____16379;
              FStar_Syntax_Syntax.sigattrs = uu____16380;_},uu____16381),uu____16382)
          -> true
      | uu____16437 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16448 = lookup_qname env lid  in
      match uu____16448 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16449,uu____16450,uu____16451,uu____16452,uu____16453,uu____16454);
              FStar_Syntax_Syntax.sigrng = uu____16455;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16457;
              FStar_Syntax_Syntax.sigattrs = uu____16458;_},uu____16459),uu____16460)
          ->
          FStar_Util.for_some
            (fun uu___231_16521  ->
               match uu___231_16521 with
               | FStar_Syntax_Syntax.RecordType uu____16522 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16531 -> true
               | uu____16540 -> false) quals
      | uu____16541 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16547,uu____16548);
            FStar_Syntax_Syntax.sigrng = uu____16549;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16551;
            FStar_Syntax_Syntax.sigattrs = uu____16552;_},uu____16553),uu____16554)
        ->
        FStar_Util.for_some
          (fun uu___232_16611  ->
             match uu___232_16611 with
             | FStar_Syntax_Syntax.Action uu____16612 -> true
             | uu____16613 -> false) quals
    | uu____16614 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16625 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16625
  
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
      let uu____16639 =
        let uu____16640 = FStar_Syntax_Util.un_uinst head1  in
        uu____16640.FStar_Syntax_Syntax.n  in
      match uu____16639 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16644 ->
               true
           | uu____16645 -> false)
      | uu____16646 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16657 = lookup_qname env l  in
      match uu____16657 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16659),uu____16660) ->
          FStar_Util.for_some
            (fun uu___233_16708  ->
               match uu___233_16708 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16709 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16710 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16781 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16797) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16814 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16821 ->
                 FStar_Pervasives_Native.Some true
             | uu____16838 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16839 =
        let uu____16842 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16842 mapper  in
      match uu____16839 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____16894 = lookup_qname env lid  in
      match uu____16894 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16897,uu____16898,tps,uu____16900,uu____16901,uu____16902);
              FStar_Syntax_Syntax.sigrng = uu____16903;
              FStar_Syntax_Syntax.sigquals = uu____16904;
              FStar_Syntax_Syntax.sigmeta = uu____16905;
              FStar_Syntax_Syntax.sigattrs = uu____16906;_},uu____16907),uu____16908)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____16973 -> FStar_Pervasives_Native.None
  
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
           (fun uu____17017  ->
              match uu____17017 with
              | (d,uu____17025) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17040 = effect_decl_opt env l  in
      match uu____17040 with
      | FStar_Pervasives_Native.None  ->
          let uu____17055 = name_not_found l  in
          let uu____17060 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17055 uu____17060
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17082  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17101  ->
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
        let uu____17132 = FStar_Ident.lid_equals l1 l2  in
        if uu____17132
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17140 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17140
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17148 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17201  ->
                        match uu____17201 with
                        | (m1,m2,uu____17214,uu____17215,uu____17216) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17148 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17233 =
                    let uu____17238 =
                      let uu____17239 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17240 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17239
                        uu____17240
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17238)
                     in
                  FStar_Errors.raise_error uu____17233 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17247,uu____17248,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17281 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17281
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
  'Auu____17297 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17297)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17326 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17352  ->
                match uu____17352 with
                | (d,uu____17358) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17326 with
      | FStar_Pervasives_Native.None  ->
          let uu____17369 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17369
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17382 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17382 with
           | (uu____17397,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17415)::(wp,uu____17417)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17473 -> failwith "Impossible"))
  
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
          let uu____17528 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17528
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17530 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17530
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
                  let uu____17538 = get_range env  in
                  let uu____17539 =
                    let uu____17546 =
                      let uu____17547 =
                        let uu____17564 =
                          let uu____17575 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17575]  in
                        (null_wp, uu____17564)  in
                      FStar_Syntax_Syntax.Tm_app uu____17547  in
                    FStar_Syntax_Syntax.mk uu____17546  in
                  uu____17539 FStar_Pervasives_Native.None uu____17538  in
                let uu____17615 =
                  let uu____17616 =
                    let uu____17627 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17627]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17616;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17615))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___248_17664 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___248_17664.order);
              joins = (uu___248_17664.joins)
            }  in
          let uu___249_17673 = env  in
          {
            solver = (uu___249_17673.solver);
            range = (uu___249_17673.range);
            curmodule = (uu___249_17673.curmodule);
            gamma = (uu___249_17673.gamma);
            gamma_sig = (uu___249_17673.gamma_sig);
            gamma_cache = (uu___249_17673.gamma_cache);
            modules = (uu___249_17673.modules);
            expected_typ = (uu___249_17673.expected_typ);
            sigtab = (uu___249_17673.sigtab);
            attrtab = (uu___249_17673.attrtab);
            is_pattern = (uu___249_17673.is_pattern);
            instantiate_imp = (uu___249_17673.instantiate_imp);
            effects;
            generalize = (uu___249_17673.generalize);
            letrecs = (uu___249_17673.letrecs);
            top_level = (uu___249_17673.top_level);
            check_uvars = (uu___249_17673.check_uvars);
            use_eq = (uu___249_17673.use_eq);
            is_iface = (uu___249_17673.is_iface);
            admit = (uu___249_17673.admit);
            lax = (uu___249_17673.lax);
            lax_universes = (uu___249_17673.lax_universes);
            phase1 = (uu___249_17673.phase1);
            failhard = (uu___249_17673.failhard);
            nosynth = (uu___249_17673.nosynth);
            uvar_subtyping = (uu___249_17673.uvar_subtyping);
            tc_term = (uu___249_17673.tc_term);
            type_of = (uu___249_17673.type_of);
            universe_of = (uu___249_17673.universe_of);
            check_type_of = (uu___249_17673.check_type_of);
            use_bv_sorts = (uu___249_17673.use_bv_sorts);
            qtbl_name_and_index = (uu___249_17673.qtbl_name_and_index);
            normalized_eff_names = (uu___249_17673.normalized_eff_names);
            proof_ns = (uu___249_17673.proof_ns);
            synth_hook = (uu___249_17673.synth_hook);
            splice = (uu___249_17673.splice);
            is_native_tactic = (uu___249_17673.is_native_tactic);
            identifier_info = (uu___249_17673.identifier_info);
            tc_hooks = (uu___249_17673.tc_hooks);
            dsenv = (uu___249_17673.dsenv);
            dep_graph = (uu___249_17673.dep_graph);
            nbe = (uu___249_17673.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17703 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17703  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____17861 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____17862 = l1 u t wp e  in
                                l2 u t uu____17861 uu____17862))
                | uu____17863 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____17935 = inst_tscheme_with lift_t [u]  in
            match uu____17935 with
            | (uu____17942,lift_t1) ->
                let uu____17944 =
                  let uu____17951 =
                    let uu____17952 =
                      let uu____17969 =
                        let uu____17980 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17989 =
                          let uu____18000 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18000]  in
                        uu____17980 :: uu____17989  in
                      (lift_t1, uu____17969)  in
                    FStar_Syntax_Syntax.Tm_app uu____17952  in
                  FStar_Syntax_Syntax.mk uu____17951  in
                uu____17944 FStar_Pervasives_Native.None
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
            let uu____18112 = inst_tscheme_with lift_t [u]  in
            match uu____18112 with
            | (uu____18119,lift_t1) ->
                let uu____18121 =
                  let uu____18128 =
                    let uu____18129 =
                      let uu____18146 =
                        let uu____18157 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18166 =
                          let uu____18177 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18186 =
                            let uu____18197 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18197]  in
                          uu____18177 :: uu____18186  in
                        uu____18157 :: uu____18166  in
                      (lift_t1, uu____18146)  in
                    FStar_Syntax_Syntax.Tm_app uu____18129  in
                  FStar_Syntax_Syntax.mk uu____18128  in
                uu____18121 FStar_Pervasives_Native.None
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
              let uu____18299 =
                let uu____18300 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18300
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18299  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18304 =
              let uu____18305 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18305  in
            let uu____18306 =
              let uu____18307 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18333 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18333)
                 in
              FStar_Util.dflt "none" uu____18307  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18304
              uu____18306
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18359  ->
                    match uu____18359 with
                    | (e,uu____18367) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18390 =
            match uu____18390 with
            | (i,j) ->
                let uu____18401 = FStar_Ident.lid_equals i j  in
                if uu____18401
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
              let uu____18433 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18443 = FStar_Ident.lid_equals i k  in
                        if uu____18443
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18454 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18454
                                  then []
                                  else
                                    (let uu____18458 =
                                       let uu____18467 =
                                         find_edge order1 (i, k)  in
                                       let uu____18470 =
                                         find_edge order1 (k, j)  in
                                       (uu____18467, uu____18470)  in
                                     match uu____18458 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18485 =
                                           compose_edges e1 e2  in
                                         [uu____18485]
                                     | uu____18486 -> [])))))
                 in
              FStar_List.append order1 uu____18433  in
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
                   let uu____18516 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18518 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18518
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18516
                   then
                     let uu____18523 =
                       let uu____18528 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18528)
                        in
                     let uu____18529 = get_range env  in
                     FStar_Errors.raise_error uu____18523 uu____18529
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18606 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18606
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18655 =
                                              let uu____18664 =
                                                find_edge order2 (i, k)  in
                                              let uu____18667 =
                                                find_edge order2 (j, k)  in
                                              (uu____18664, uu____18667)  in
                                            match uu____18655 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18709,uu____18710)
                                                     ->
                                                     let uu____18717 =
                                                       let uu____18722 =
                                                         let uu____18723 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18723
                                                          in
                                                       let uu____18726 =
                                                         let uu____18727 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18727
                                                          in
                                                       (uu____18722,
                                                         uu____18726)
                                                        in
                                                     (match uu____18717 with
                                                      | (true ,true ) ->
                                                          let uu____18738 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18738
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
                                            | uu____18763 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___250_18836 = env.effects  in
              { decls = (uu___250_18836.decls); order = order2; joins }  in
            let uu___251_18837 = env  in
            {
              solver = (uu___251_18837.solver);
              range = (uu___251_18837.range);
              curmodule = (uu___251_18837.curmodule);
              gamma = (uu___251_18837.gamma);
              gamma_sig = (uu___251_18837.gamma_sig);
              gamma_cache = (uu___251_18837.gamma_cache);
              modules = (uu___251_18837.modules);
              expected_typ = (uu___251_18837.expected_typ);
              sigtab = (uu___251_18837.sigtab);
              attrtab = (uu___251_18837.attrtab);
              is_pattern = (uu___251_18837.is_pattern);
              instantiate_imp = (uu___251_18837.instantiate_imp);
              effects;
              generalize = (uu___251_18837.generalize);
              letrecs = (uu___251_18837.letrecs);
              top_level = (uu___251_18837.top_level);
              check_uvars = (uu___251_18837.check_uvars);
              use_eq = (uu___251_18837.use_eq);
              is_iface = (uu___251_18837.is_iface);
              admit = (uu___251_18837.admit);
              lax = (uu___251_18837.lax);
              lax_universes = (uu___251_18837.lax_universes);
              phase1 = (uu___251_18837.phase1);
              failhard = (uu___251_18837.failhard);
              nosynth = (uu___251_18837.nosynth);
              uvar_subtyping = (uu___251_18837.uvar_subtyping);
              tc_term = (uu___251_18837.tc_term);
              type_of = (uu___251_18837.type_of);
              universe_of = (uu___251_18837.universe_of);
              check_type_of = (uu___251_18837.check_type_of);
              use_bv_sorts = (uu___251_18837.use_bv_sorts);
              qtbl_name_and_index = (uu___251_18837.qtbl_name_and_index);
              normalized_eff_names = (uu___251_18837.normalized_eff_names);
              proof_ns = (uu___251_18837.proof_ns);
              synth_hook = (uu___251_18837.synth_hook);
              splice = (uu___251_18837.splice);
              is_native_tactic = (uu___251_18837.is_native_tactic);
              identifier_info = (uu___251_18837.identifier_info);
              tc_hooks = (uu___251_18837.tc_hooks);
              dsenv = (uu___251_18837.dsenv);
              dep_graph = (uu___251_18837.dep_graph);
              nbe = (uu___251_18837.nbe)
            }))
      | uu____18838 -> env
  
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
        | uu____18866 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____18878 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____18878 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____18895 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____18895 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18917 =
                     let uu____18922 =
                       let uu____18923 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____18930 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____18939 =
                         let uu____18940 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____18940  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18923 uu____18930 uu____18939
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18922)
                      in
                   FStar_Errors.raise_error uu____18917
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____18945 =
                     let uu____18956 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____18956 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____18993  ->
                        fun uu____18994  ->
                          match (uu____18993, uu____18994) with
                          | ((x,uu____19024),(t,uu____19026)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____18945
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19057 =
                     let uu___252_19058 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___252_19058.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___252_19058.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___252_19058.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___252_19058.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19057
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____19069 .
    'Auu____19069 ->
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
          let uu____19099 = effect_decl_opt env effect_name  in
          match uu____19099 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____19138 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19161 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____19198 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____19198
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____19199 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19199
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____19213 =
                     let uu____19216 = get_range env  in
                     let uu____19217 =
                       let uu____19224 =
                         let uu____19225 =
                           let uu____19242 =
                             let uu____19253 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____19253; wp]  in
                           (repr, uu____19242)  in
                         FStar_Syntax_Syntax.Tm_app uu____19225  in
                       FStar_Syntax_Syntax.mk uu____19224  in
                     uu____19217 FStar_Pervasives_Native.None uu____19216  in
                   FStar_Pervasives_Native.Some uu____19213)
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      (is_user_reifiable_effect env effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
  
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____19368 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19379 =
        let uu____19380 = FStar_Syntax_Subst.compress t  in
        uu____19380.FStar_Syntax_Syntax.n  in
      match uu____19379 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19383,c) ->
          is_reifiable_comp env c
      | uu____19405 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____19423 =
           let uu____19424 = is_reifiable_effect env l  in
           Prims.op_Negation uu____19424  in
         if uu____19423
         then
           let uu____19425 =
             let uu____19430 =
               let uu____19431 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19431
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19430)  in
           let uu____19432 = get_range env  in
           FStar_Errors.raise_error uu____19425 uu____19432
         else ());
        (let uu____19434 = effect_repr_aux true env c u_c  in
         match uu____19434 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___253_19466 = env  in
        {
          solver = (uu___253_19466.solver);
          range = (uu___253_19466.range);
          curmodule = (uu___253_19466.curmodule);
          gamma = (uu___253_19466.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___253_19466.gamma_cache);
          modules = (uu___253_19466.modules);
          expected_typ = (uu___253_19466.expected_typ);
          sigtab = (uu___253_19466.sigtab);
          attrtab = (uu___253_19466.attrtab);
          is_pattern = (uu___253_19466.is_pattern);
          instantiate_imp = (uu___253_19466.instantiate_imp);
          effects = (uu___253_19466.effects);
          generalize = (uu___253_19466.generalize);
          letrecs = (uu___253_19466.letrecs);
          top_level = (uu___253_19466.top_level);
          check_uvars = (uu___253_19466.check_uvars);
          use_eq = (uu___253_19466.use_eq);
          is_iface = (uu___253_19466.is_iface);
          admit = (uu___253_19466.admit);
          lax = (uu___253_19466.lax);
          lax_universes = (uu___253_19466.lax_universes);
          phase1 = (uu___253_19466.phase1);
          failhard = (uu___253_19466.failhard);
          nosynth = (uu___253_19466.nosynth);
          uvar_subtyping = (uu___253_19466.uvar_subtyping);
          tc_term = (uu___253_19466.tc_term);
          type_of = (uu___253_19466.type_of);
          universe_of = (uu___253_19466.universe_of);
          check_type_of = (uu___253_19466.check_type_of);
          use_bv_sorts = (uu___253_19466.use_bv_sorts);
          qtbl_name_and_index = (uu___253_19466.qtbl_name_and_index);
          normalized_eff_names = (uu___253_19466.normalized_eff_names);
          proof_ns = (uu___253_19466.proof_ns);
          synth_hook = (uu___253_19466.synth_hook);
          splice = (uu___253_19466.splice);
          is_native_tactic = (uu___253_19466.is_native_tactic);
          identifier_info = (uu___253_19466.identifier_info);
          tc_hooks = (uu___253_19466.tc_hooks);
          dsenv = (uu___253_19466.dsenv);
          dep_graph = (uu___253_19466.dep_graph);
          nbe = (uu___253_19466.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___254_19479 = env  in
      {
        solver = (uu___254_19479.solver);
        range = (uu___254_19479.range);
        curmodule = (uu___254_19479.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___254_19479.gamma_sig);
        gamma_cache = (uu___254_19479.gamma_cache);
        modules = (uu___254_19479.modules);
        expected_typ = (uu___254_19479.expected_typ);
        sigtab = (uu___254_19479.sigtab);
        attrtab = (uu___254_19479.attrtab);
        is_pattern = (uu___254_19479.is_pattern);
        instantiate_imp = (uu___254_19479.instantiate_imp);
        effects = (uu___254_19479.effects);
        generalize = (uu___254_19479.generalize);
        letrecs = (uu___254_19479.letrecs);
        top_level = (uu___254_19479.top_level);
        check_uvars = (uu___254_19479.check_uvars);
        use_eq = (uu___254_19479.use_eq);
        is_iface = (uu___254_19479.is_iface);
        admit = (uu___254_19479.admit);
        lax = (uu___254_19479.lax);
        lax_universes = (uu___254_19479.lax_universes);
        phase1 = (uu___254_19479.phase1);
        failhard = (uu___254_19479.failhard);
        nosynth = (uu___254_19479.nosynth);
        uvar_subtyping = (uu___254_19479.uvar_subtyping);
        tc_term = (uu___254_19479.tc_term);
        type_of = (uu___254_19479.type_of);
        universe_of = (uu___254_19479.universe_of);
        check_type_of = (uu___254_19479.check_type_of);
        use_bv_sorts = (uu___254_19479.use_bv_sorts);
        qtbl_name_and_index = (uu___254_19479.qtbl_name_and_index);
        normalized_eff_names = (uu___254_19479.normalized_eff_names);
        proof_ns = (uu___254_19479.proof_ns);
        synth_hook = (uu___254_19479.synth_hook);
        splice = (uu___254_19479.splice);
        is_native_tactic = (uu___254_19479.is_native_tactic);
        identifier_info = (uu___254_19479.identifier_info);
        tc_hooks = (uu___254_19479.tc_hooks);
        dsenv = (uu___254_19479.dsenv);
        dep_graph = (uu___254_19479.dep_graph);
        nbe = (uu___254_19479.nbe)
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
            (let uu___255_19534 = env  in
             {
               solver = (uu___255_19534.solver);
               range = (uu___255_19534.range);
               curmodule = (uu___255_19534.curmodule);
               gamma = rest;
               gamma_sig = (uu___255_19534.gamma_sig);
               gamma_cache = (uu___255_19534.gamma_cache);
               modules = (uu___255_19534.modules);
               expected_typ = (uu___255_19534.expected_typ);
               sigtab = (uu___255_19534.sigtab);
               attrtab = (uu___255_19534.attrtab);
               is_pattern = (uu___255_19534.is_pattern);
               instantiate_imp = (uu___255_19534.instantiate_imp);
               effects = (uu___255_19534.effects);
               generalize = (uu___255_19534.generalize);
               letrecs = (uu___255_19534.letrecs);
               top_level = (uu___255_19534.top_level);
               check_uvars = (uu___255_19534.check_uvars);
               use_eq = (uu___255_19534.use_eq);
               is_iface = (uu___255_19534.is_iface);
               admit = (uu___255_19534.admit);
               lax = (uu___255_19534.lax);
               lax_universes = (uu___255_19534.lax_universes);
               phase1 = (uu___255_19534.phase1);
               failhard = (uu___255_19534.failhard);
               nosynth = (uu___255_19534.nosynth);
               uvar_subtyping = (uu___255_19534.uvar_subtyping);
               tc_term = (uu___255_19534.tc_term);
               type_of = (uu___255_19534.type_of);
               universe_of = (uu___255_19534.universe_of);
               check_type_of = (uu___255_19534.check_type_of);
               use_bv_sorts = (uu___255_19534.use_bv_sorts);
               qtbl_name_and_index = (uu___255_19534.qtbl_name_and_index);
               normalized_eff_names = (uu___255_19534.normalized_eff_names);
               proof_ns = (uu___255_19534.proof_ns);
               synth_hook = (uu___255_19534.synth_hook);
               splice = (uu___255_19534.splice);
               is_native_tactic = (uu___255_19534.is_native_tactic);
               identifier_info = (uu___255_19534.identifier_info);
               tc_hooks = (uu___255_19534.tc_hooks);
               dsenv = (uu___255_19534.dsenv);
               dep_graph = (uu___255_19534.dep_graph);
               nbe = (uu___255_19534.nbe)
             }))
    | uu____19535 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19563  ->
             match uu____19563 with | (x,uu____19571) -> push_bv env1 x) env
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
            let uu___256_19605 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___256_19605.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___256_19605.FStar_Syntax_Syntax.index);
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
      (let uu___257_19645 = env  in
       {
         solver = (uu___257_19645.solver);
         range = (uu___257_19645.range);
         curmodule = (uu___257_19645.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_19645.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___257_19645.sigtab);
         attrtab = (uu___257_19645.attrtab);
         is_pattern = (uu___257_19645.is_pattern);
         instantiate_imp = (uu___257_19645.instantiate_imp);
         effects = (uu___257_19645.effects);
         generalize = (uu___257_19645.generalize);
         letrecs = (uu___257_19645.letrecs);
         top_level = (uu___257_19645.top_level);
         check_uvars = (uu___257_19645.check_uvars);
         use_eq = (uu___257_19645.use_eq);
         is_iface = (uu___257_19645.is_iface);
         admit = (uu___257_19645.admit);
         lax = (uu___257_19645.lax);
         lax_universes = (uu___257_19645.lax_universes);
         phase1 = (uu___257_19645.phase1);
         failhard = (uu___257_19645.failhard);
         nosynth = (uu___257_19645.nosynth);
         uvar_subtyping = (uu___257_19645.uvar_subtyping);
         tc_term = (uu___257_19645.tc_term);
         type_of = (uu___257_19645.type_of);
         universe_of = (uu___257_19645.universe_of);
         check_type_of = (uu___257_19645.check_type_of);
         use_bv_sorts = (uu___257_19645.use_bv_sorts);
         qtbl_name_and_index = (uu___257_19645.qtbl_name_and_index);
         normalized_eff_names = (uu___257_19645.normalized_eff_names);
         proof_ns = (uu___257_19645.proof_ns);
         synth_hook = (uu___257_19645.synth_hook);
         splice = (uu___257_19645.splice);
         is_native_tactic = (uu___257_19645.is_native_tactic);
         identifier_info = (uu___257_19645.identifier_info);
         tc_hooks = (uu___257_19645.tc_hooks);
         dsenv = (uu___257_19645.dsenv);
         dep_graph = (uu___257_19645.dep_graph);
         nbe = (uu___257_19645.nbe)
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
        let uu____19687 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19687 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19715 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19715)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___258_19730 = env  in
      {
        solver = (uu___258_19730.solver);
        range = (uu___258_19730.range);
        curmodule = (uu___258_19730.curmodule);
        gamma = (uu___258_19730.gamma);
        gamma_sig = (uu___258_19730.gamma_sig);
        gamma_cache = (uu___258_19730.gamma_cache);
        modules = (uu___258_19730.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___258_19730.sigtab);
        attrtab = (uu___258_19730.attrtab);
        is_pattern = (uu___258_19730.is_pattern);
        instantiate_imp = (uu___258_19730.instantiate_imp);
        effects = (uu___258_19730.effects);
        generalize = (uu___258_19730.generalize);
        letrecs = (uu___258_19730.letrecs);
        top_level = (uu___258_19730.top_level);
        check_uvars = (uu___258_19730.check_uvars);
        use_eq = false;
        is_iface = (uu___258_19730.is_iface);
        admit = (uu___258_19730.admit);
        lax = (uu___258_19730.lax);
        lax_universes = (uu___258_19730.lax_universes);
        phase1 = (uu___258_19730.phase1);
        failhard = (uu___258_19730.failhard);
        nosynth = (uu___258_19730.nosynth);
        uvar_subtyping = (uu___258_19730.uvar_subtyping);
        tc_term = (uu___258_19730.tc_term);
        type_of = (uu___258_19730.type_of);
        universe_of = (uu___258_19730.universe_of);
        check_type_of = (uu___258_19730.check_type_of);
        use_bv_sorts = (uu___258_19730.use_bv_sorts);
        qtbl_name_and_index = (uu___258_19730.qtbl_name_and_index);
        normalized_eff_names = (uu___258_19730.normalized_eff_names);
        proof_ns = (uu___258_19730.proof_ns);
        synth_hook = (uu___258_19730.synth_hook);
        splice = (uu___258_19730.splice);
        is_native_tactic = (uu___258_19730.is_native_tactic);
        identifier_info = (uu___258_19730.identifier_info);
        tc_hooks = (uu___258_19730.tc_hooks);
        dsenv = (uu___258_19730.dsenv);
        dep_graph = (uu___258_19730.dep_graph);
        nbe = (uu___258_19730.nbe)
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
    let uu____19758 = expected_typ env_  in
    ((let uu___259_19764 = env_  in
      {
        solver = (uu___259_19764.solver);
        range = (uu___259_19764.range);
        curmodule = (uu___259_19764.curmodule);
        gamma = (uu___259_19764.gamma);
        gamma_sig = (uu___259_19764.gamma_sig);
        gamma_cache = (uu___259_19764.gamma_cache);
        modules = (uu___259_19764.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___259_19764.sigtab);
        attrtab = (uu___259_19764.attrtab);
        is_pattern = (uu___259_19764.is_pattern);
        instantiate_imp = (uu___259_19764.instantiate_imp);
        effects = (uu___259_19764.effects);
        generalize = (uu___259_19764.generalize);
        letrecs = (uu___259_19764.letrecs);
        top_level = (uu___259_19764.top_level);
        check_uvars = (uu___259_19764.check_uvars);
        use_eq = false;
        is_iface = (uu___259_19764.is_iface);
        admit = (uu___259_19764.admit);
        lax = (uu___259_19764.lax);
        lax_universes = (uu___259_19764.lax_universes);
        phase1 = (uu___259_19764.phase1);
        failhard = (uu___259_19764.failhard);
        nosynth = (uu___259_19764.nosynth);
        uvar_subtyping = (uu___259_19764.uvar_subtyping);
        tc_term = (uu___259_19764.tc_term);
        type_of = (uu___259_19764.type_of);
        universe_of = (uu___259_19764.universe_of);
        check_type_of = (uu___259_19764.check_type_of);
        use_bv_sorts = (uu___259_19764.use_bv_sorts);
        qtbl_name_and_index = (uu___259_19764.qtbl_name_and_index);
        normalized_eff_names = (uu___259_19764.normalized_eff_names);
        proof_ns = (uu___259_19764.proof_ns);
        synth_hook = (uu___259_19764.synth_hook);
        splice = (uu___259_19764.splice);
        is_native_tactic = (uu___259_19764.is_native_tactic);
        identifier_info = (uu___259_19764.identifier_info);
        tc_hooks = (uu___259_19764.tc_hooks);
        dsenv = (uu___259_19764.dsenv);
        dep_graph = (uu___259_19764.dep_graph);
        nbe = (uu___259_19764.nbe)
      }), uu____19758)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19774 =
      let uu____19777 = FStar_Ident.id_of_text ""  in [uu____19777]  in
    FStar_Ident.lid_of_ids uu____19774  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19783 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19783
        then
          let uu____19786 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19786 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___260_19813 = env  in
       {
         solver = (uu___260_19813.solver);
         range = (uu___260_19813.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___260_19813.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___260_19813.expected_typ);
         sigtab = (uu___260_19813.sigtab);
         attrtab = (uu___260_19813.attrtab);
         is_pattern = (uu___260_19813.is_pattern);
         instantiate_imp = (uu___260_19813.instantiate_imp);
         effects = (uu___260_19813.effects);
         generalize = (uu___260_19813.generalize);
         letrecs = (uu___260_19813.letrecs);
         top_level = (uu___260_19813.top_level);
         check_uvars = (uu___260_19813.check_uvars);
         use_eq = (uu___260_19813.use_eq);
         is_iface = (uu___260_19813.is_iface);
         admit = (uu___260_19813.admit);
         lax = (uu___260_19813.lax);
         lax_universes = (uu___260_19813.lax_universes);
         phase1 = (uu___260_19813.phase1);
         failhard = (uu___260_19813.failhard);
         nosynth = (uu___260_19813.nosynth);
         uvar_subtyping = (uu___260_19813.uvar_subtyping);
         tc_term = (uu___260_19813.tc_term);
         type_of = (uu___260_19813.type_of);
         universe_of = (uu___260_19813.universe_of);
         check_type_of = (uu___260_19813.check_type_of);
         use_bv_sorts = (uu___260_19813.use_bv_sorts);
         qtbl_name_and_index = (uu___260_19813.qtbl_name_and_index);
         normalized_eff_names = (uu___260_19813.normalized_eff_names);
         proof_ns = (uu___260_19813.proof_ns);
         synth_hook = (uu___260_19813.synth_hook);
         splice = (uu___260_19813.splice);
         is_native_tactic = (uu___260_19813.is_native_tactic);
         identifier_info = (uu___260_19813.identifier_info);
         tc_hooks = (uu___260_19813.tc_hooks);
         dsenv = (uu___260_19813.dsenv);
         dep_graph = (uu___260_19813.dep_graph);
         nbe = (uu___260_19813.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19864)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19868,(uu____19869,t)))::tl1
          ->
          let uu____19890 =
            let uu____19893 = FStar_Syntax_Free.uvars t  in
            ext out uu____19893  in
          aux uu____19890 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19896;
            FStar_Syntax_Syntax.index = uu____19897;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19904 =
            let uu____19907 = FStar_Syntax_Free.uvars t  in
            ext out uu____19907  in
          aux uu____19904 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19964)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19968,(uu____19969,t)))::tl1
          ->
          let uu____19990 =
            let uu____19993 = FStar_Syntax_Free.univs t  in
            ext out uu____19993  in
          aux uu____19990 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19996;
            FStar_Syntax_Syntax.index = uu____19997;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20004 =
            let uu____20007 = FStar_Syntax_Free.univs t  in
            ext out uu____20007  in
          aux uu____20004 tl1
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
          let uu____20068 = FStar_Util.set_add uname out  in
          aux uu____20068 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20071,(uu____20072,t)))::tl1
          ->
          let uu____20093 =
            let uu____20096 = FStar_Syntax_Free.univnames t  in
            ext out uu____20096  in
          aux uu____20093 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20099;
            FStar_Syntax_Syntax.index = uu____20100;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20107 =
            let uu____20110 = FStar_Syntax_Free.univnames t  in
            ext out uu____20110  in
          aux uu____20107 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___234_20130  ->
            match uu___234_20130 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20134 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20147 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20157 =
      let uu____20166 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20166
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20157 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20210 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___235_20220  ->
              match uu___235_20220 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20222 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20222
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20225) ->
                  let uu____20242 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20242))
       in
    FStar_All.pipe_right uu____20210 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___236_20249  ->
    match uu___236_20249 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20251 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20251
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20271  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20313) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20332,uu____20333) -> false  in
      let uu____20342 =
        FStar_List.tryFind
          (fun uu____20360  ->
             match uu____20360 with | (p,uu____20368) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20342 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20379,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20401 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20401
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___261_20419 = e  in
        {
          solver = (uu___261_20419.solver);
          range = (uu___261_20419.range);
          curmodule = (uu___261_20419.curmodule);
          gamma = (uu___261_20419.gamma);
          gamma_sig = (uu___261_20419.gamma_sig);
          gamma_cache = (uu___261_20419.gamma_cache);
          modules = (uu___261_20419.modules);
          expected_typ = (uu___261_20419.expected_typ);
          sigtab = (uu___261_20419.sigtab);
          attrtab = (uu___261_20419.attrtab);
          is_pattern = (uu___261_20419.is_pattern);
          instantiate_imp = (uu___261_20419.instantiate_imp);
          effects = (uu___261_20419.effects);
          generalize = (uu___261_20419.generalize);
          letrecs = (uu___261_20419.letrecs);
          top_level = (uu___261_20419.top_level);
          check_uvars = (uu___261_20419.check_uvars);
          use_eq = (uu___261_20419.use_eq);
          is_iface = (uu___261_20419.is_iface);
          admit = (uu___261_20419.admit);
          lax = (uu___261_20419.lax);
          lax_universes = (uu___261_20419.lax_universes);
          phase1 = (uu___261_20419.phase1);
          failhard = (uu___261_20419.failhard);
          nosynth = (uu___261_20419.nosynth);
          uvar_subtyping = (uu___261_20419.uvar_subtyping);
          tc_term = (uu___261_20419.tc_term);
          type_of = (uu___261_20419.type_of);
          universe_of = (uu___261_20419.universe_of);
          check_type_of = (uu___261_20419.check_type_of);
          use_bv_sorts = (uu___261_20419.use_bv_sorts);
          qtbl_name_and_index = (uu___261_20419.qtbl_name_and_index);
          normalized_eff_names = (uu___261_20419.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___261_20419.synth_hook);
          splice = (uu___261_20419.splice);
          is_native_tactic = (uu___261_20419.is_native_tactic);
          identifier_info = (uu___261_20419.identifier_info);
          tc_hooks = (uu___261_20419.tc_hooks);
          dsenv = (uu___261_20419.dsenv);
          dep_graph = (uu___261_20419.dep_graph);
          nbe = (uu___261_20419.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___262_20459 = e  in
      {
        solver = (uu___262_20459.solver);
        range = (uu___262_20459.range);
        curmodule = (uu___262_20459.curmodule);
        gamma = (uu___262_20459.gamma);
        gamma_sig = (uu___262_20459.gamma_sig);
        gamma_cache = (uu___262_20459.gamma_cache);
        modules = (uu___262_20459.modules);
        expected_typ = (uu___262_20459.expected_typ);
        sigtab = (uu___262_20459.sigtab);
        attrtab = (uu___262_20459.attrtab);
        is_pattern = (uu___262_20459.is_pattern);
        instantiate_imp = (uu___262_20459.instantiate_imp);
        effects = (uu___262_20459.effects);
        generalize = (uu___262_20459.generalize);
        letrecs = (uu___262_20459.letrecs);
        top_level = (uu___262_20459.top_level);
        check_uvars = (uu___262_20459.check_uvars);
        use_eq = (uu___262_20459.use_eq);
        is_iface = (uu___262_20459.is_iface);
        admit = (uu___262_20459.admit);
        lax = (uu___262_20459.lax);
        lax_universes = (uu___262_20459.lax_universes);
        phase1 = (uu___262_20459.phase1);
        failhard = (uu___262_20459.failhard);
        nosynth = (uu___262_20459.nosynth);
        uvar_subtyping = (uu___262_20459.uvar_subtyping);
        tc_term = (uu___262_20459.tc_term);
        type_of = (uu___262_20459.type_of);
        universe_of = (uu___262_20459.universe_of);
        check_type_of = (uu___262_20459.check_type_of);
        use_bv_sorts = (uu___262_20459.use_bv_sorts);
        qtbl_name_and_index = (uu___262_20459.qtbl_name_and_index);
        normalized_eff_names = (uu___262_20459.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___262_20459.synth_hook);
        splice = (uu___262_20459.splice);
        is_native_tactic = (uu___262_20459.is_native_tactic);
        identifier_info = (uu___262_20459.identifier_info);
        tc_hooks = (uu___262_20459.tc_hooks);
        dsenv = (uu___262_20459.dsenv);
        dep_graph = (uu___262_20459.dep_graph);
        nbe = (uu___262_20459.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20474 = FStar_Syntax_Free.names t  in
      let uu____20477 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20474 uu____20477
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20498 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20498
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20506 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20506
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20523 =
      match uu____20523 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20533 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20533)
       in
    let uu____20535 =
      let uu____20538 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20538 FStar_List.rev  in
    FStar_All.pipe_right uu____20535 (FStar_String.concat " ")
  
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
                  (let uu____20591 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20591 with
                   | FStar_Pervasives_Native.Some uu____20594 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20595 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20601;
        univ_ineqs = uu____20602; implicits = uu____20603;_} -> true
    | uu____20614 -> false
  
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
          let uu___263_20641 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___263_20641.deferred);
            univ_ineqs = (uu___263_20641.univ_ineqs);
            implicits = (uu___263_20641.implicits)
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
          let uu____20676 = FStar_Options.defensive ()  in
          if uu____20676
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20680 =
              let uu____20681 =
                let uu____20682 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20682  in
              Prims.op_Negation uu____20681  in
            (if uu____20680
             then
               let uu____20687 =
                 let uu____20692 =
                   let uu____20693 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20694 =
                     let uu____20695 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20695
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20693 uu____20694
                    in
                 (FStar_Errors.Warning_Defensive, uu____20692)  in
               FStar_Errors.log_issue rng uu____20687
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
          let uu____20726 =
            let uu____20727 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20727  in
          if uu____20726
          then ()
          else
            (let uu____20729 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20729 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20752 =
            let uu____20753 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20753  in
          if uu____20752
          then ()
          else
            (let uu____20755 = bound_vars e  in
             def_check_closed_in rng msg uu____20755 t)
  
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
          let uu___264_20790 = g  in
          let uu____20791 =
            let uu____20792 =
              let uu____20793 =
                let uu____20800 =
                  let uu____20801 =
                    let uu____20818 =
                      let uu____20829 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20829]  in
                    (f, uu____20818)  in
                  FStar_Syntax_Syntax.Tm_app uu____20801  in
                FStar_Syntax_Syntax.mk uu____20800  in
              uu____20793 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20792
             in
          {
            guard_f = uu____20791;
            deferred = (uu___264_20790.deferred);
            univ_ineqs = (uu___264_20790.univ_ineqs);
            implicits = (uu___264_20790.implicits)
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
          let uu___265_20885 = g  in
          let uu____20886 =
            let uu____20887 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20887  in
          {
            guard_f = uu____20886;
            deferred = (uu___265_20885.deferred);
            univ_ineqs = (uu___265_20885.univ_ineqs);
            implicits = (uu___265_20885.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___266_20903 = g  in
          let uu____20904 =
            let uu____20905 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____20905  in
          {
            guard_f = uu____20904;
            deferred = (uu___266_20903.deferred);
            univ_ineqs = (uu___266_20903.univ_ineqs);
            implicits = (uu___266_20903.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___267_20907 = g  in
          let uu____20908 =
            let uu____20909 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20909  in
          {
            guard_f = uu____20908;
            deferred = (uu___267_20907.deferred);
            univ_ineqs = (uu___267_20907.univ_ineqs);
            implicits = (uu___267_20907.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20915 ->
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
          let uu____20930 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____20930
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____20936 =
      let uu____20937 = FStar_Syntax_Util.unmeta t  in
      uu____20937.FStar_Syntax_Syntax.n  in
    match uu____20936 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____20941 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____20982 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____20982;
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
                       let uu____21063 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21063
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___268_21067 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___268_21067.deferred);
              univ_ineqs = (uu___268_21067.univ_ineqs);
              implicits = (uu___268_21067.implicits)
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
               let uu____21100 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21100
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
            let uu___269_21123 = g  in
            let uu____21124 =
              let uu____21125 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21125  in
            {
              guard_f = uu____21124;
              deferred = (uu___269_21123.deferred);
              univ_ineqs = (uu___269_21123.univ_ineqs);
              implicits = (uu___269_21123.implicits)
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
            let uu____21163 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21163 with
            | FStar_Pervasives_Native.Some
                (uu____21188::(tm,uu____21190)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21254 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21272 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21272;
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
                    let uu___270_21307 = trivial_guard  in
                    {
                      guard_f = (uu___270_21307.guard_f);
                      deferred = (uu___270_21307.deferred);
                      univ_ineqs = (uu___270_21307.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21324  -> ());
    push = (fun uu____21326  -> ());
    pop = (fun uu____21328  -> ());
    snapshot =
      (fun uu____21330  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21339  -> fun uu____21340  -> ());
    encode_modul = (fun uu____21351  -> fun uu____21352  -> ());
    encode_sig = (fun uu____21355  -> fun uu____21356  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21362 =
             let uu____21369 = FStar_Options.peek ()  in (e, g, uu____21369)
              in
           [uu____21362]);
    solve = (fun uu____21385  -> fun uu____21386  -> fun uu____21387  -> ());
    finish = (fun uu____21393  -> ());
    refresh = (fun uu____21395  -> ())
  } 