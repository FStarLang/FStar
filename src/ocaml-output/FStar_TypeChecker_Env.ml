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
                  let uu____10167 = FStar_Syntax_DsEnv.empty_env ()  in
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
      | ((formals,t),uu____12045) ->
          let vs = mk_univ_subst formals us  in
          let uu____12069 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12069)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___224_12085  ->
    match uu___224_12085 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12111  -> new_u_univ ()))
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
      let uu____12130 = inst_tscheme t  in
      match uu____12130 with
      | (us,t1) ->
          let uu____12141 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12141)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12161  ->
          match uu____12161 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12182 =
                         let uu____12183 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12184 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12185 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12186 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12183 uu____12184 uu____12185 uu____12186
                          in
                       failwith uu____12182)
                    else ();
                    (let uu____12188 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12188))
               | uu____12197 ->
                   let uu____12198 =
                     let uu____12199 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12199
                      in
                   failwith uu____12198)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12205 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12211 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12217 -> false
  
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
             | ([],uu____12259) -> Maybe
             | (uu____12266,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12285 -> No  in
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
          let uu____12376 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12376 with
          | FStar_Pervasives_Native.None  ->
              let uu____12399 =
                FStar_Util.find_map env.gamma
                  (fun uu___225_12443  ->
                     match uu___225_12443 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12482 = FStar_Ident.lid_equals lid l  in
                         if uu____12482
                         then
                           let uu____12503 =
                             let uu____12522 =
                               let uu____12537 = inst_tscheme t  in
                               FStar_Util.Inl uu____12537  in
                             let uu____12552 = FStar_Ident.range_of_lid l  in
                             (uu____12522, uu____12552)  in
                           FStar_Pervasives_Native.Some uu____12503
                         else FStar_Pervasives_Native.None
                     | uu____12604 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12399
                (fun uu____12642  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___226_12651  ->
                        match uu___226_12651 with
                        | (uu____12654,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12656);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12657;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12658;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12659;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12660;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12680 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12680
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
                                  uu____12728 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12735 -> cache t  in
                            let uu____12736 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12736 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12742 =
                                   let uu____12743 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12743)
                                    in
                                 maybe_cache uu____12742)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12811 = find_in_sigtab env lid  in
         match uu____12811 with
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
      let uu____12891 = lookup_qname env lid  in
      match uu____12891 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12912,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13023 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13023 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13065 =
          let uu____13068 = lookup_attr env1 attr  in se1 :: uu____13068  in
        FStar_Util.smap_add (attrtab env1) attr uu____13065  in
      FStar_List.iter
        (fun attr  ->
           let uu____13078 =
             let uu____13079 = FStar_Syntax_Subst.compress attr  in
             uu____13079.FStar_Syntax_Syntax.n  in
           match uu____13078 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13083 =
                 let uu____13084 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13084.FStar_Ident.str  in
               add_one1 env se uu____13083
           | uu____13085 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13107) ->
          add_sigelts env ses
      | uu____13116 ->
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
            | uu____13131 -> ()))

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
        (fun uu___227_13162  ->
           match uu___227_13162 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13180 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13241,lb::[]),uu____13243) ->
            let uu____13250 =
              let uu____13259 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13268 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13259, uu____13268)  in
            FStar_Pervasives_Native.Some uu____13250
        | FStar_Syntax_Syntax.Sig_let ((uu____13281,lbs),uu____13283) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13313 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13325 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13325
                     then
                       let uu____13336 =
                         let uu____13345 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13354 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13345, uu____13354)  in
                       FStar_Pervasives_Native.Some uu____13336
                     else FStar_Pervasives_Native.None)
        | uu____13376 -> FStar_Pervasives_Native.None
  
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
          let uu____13435 =
            let uu____13444 =
              let uu____13449 =
                let uu____13450 =
                  let uu____13453 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13453
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13450)  in
              inst_tscheme1 uu____13449  in
            (uu____13444, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13435
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13475,uu____13476) ->
          let uu____13481 =
            let uu____13490 =
              let uu____13495 =
                let uu____13496 =
                  let uu____13499 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13499  in
                (us, uu____13496)  in
              inst_tscheme1 uu____13495  in
            (uu____13490, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13481
      | uu____13518 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13606 =
          match uu____13606 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13702,uvs,t,uu____13705,uu____13706,uu____13707);
                      FStar_Syntax_Syntax.sigrng = uu____13708;
                      FStar_Syntax_Syntax.sigquals = uu____13709;
                      FStar_Syntax_Syntax.sigmeta = uu____13710;
                      FStar_Syntax_Syntax.sigattrs = uu____13711;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13732 =
                     let uu____13741 = inst_tscheme1 (uvs, t)  in
                     (uu____13741, rng)  in
                   FStar_Pervasives_Native.Some uu____13732
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13765;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13767;
                      FStar_Syntax_Syntax.sigattrs = uu____13768;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13785 =
                     let uu____13786 = in_cur_mod env l  in uu____13786 = Yes
                      in
                   if uu____13785
                   then
                     let uu____13797 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13797
                      then
                        let uu____13810 =
                          let uu____13819 = inst_tscheme1 (uvs, t)  in
                          (uu____13819, rng)  in
                        FStar_Pervasives_Native.Some uu____13810
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13850 =
                        let uu____13859 = inst_tscheme1 (uvs, t)  in
                        (uu____13859, rng)  in
                      FStar_Pervasives_Native.Some uu____13850)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13884,uu____13885);
                      FStar_Syntax_Syntax.sigrng = uu____13886;
                      FStar_Syntax_Syntax.sigquals = uu____13887;
                      FStar_Syntax_Syntax.sigmeta = uu____13888;
                      FStar_Syntax_Syntax.sigattrs = uu____13889;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13930 =
                          let uu____13939 = inst_tscheme1 (uvs, k)  in
                          (uu____13939, rng)  in
                        FStar_Pervasives_Native.Some uu____13930
                    | uu____13960 ->
                        let uu____13961 =
                          let uu____13970 =
                            let uu____13975 =
                              let uu____13976 =
                                let uu____13979 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13979
                                 in
                              (uvs, uu____13976)  in
                            inst_tscheme1 uu____13975  in
                          (uu____13970, rng)  in
                        FStar_Pervasives_Native.Some uu____13961)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14002,uu____14003);
                      FStar_Syntax_Syntax.sigrng = uu____14004;
                      FStar_Syntax_Syntax.sigquals = uu____14005;
                      FStar_Syntax_Syntax.sigmeta = uu____14006;
                      FStar_Syntax_Syntax.sigattrs = uu____14007;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14049 =
                          let uu____14058 = inst_tscheme_with (uvs, k) us  in
                          (uu____14058, rng)  in
                        FStar_Pervasives_Native.Some uu____14049
                    | uu____14079 ->
                        let uu____14080 =
                          let uu____14089 =
                            let uu____14094 =
                              let uu____14095 =
                                let uu____14098 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14098
                                 in
                              (uvs, uu____14095)  in
                            inst_tscheme_with uu____14094 us  in
                          (uu____14089, rng)  in
                        FStar_Pervasives_Native.Some uu____14080)
               | FStar_Util.Inr se ->
                   let uu____14134 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14155;
                          FStar_Syntax_Syntax.sigrng = uu____14156;
                          FStar_Syntax_Syntax.sigquals = uu____14157;
                          FStar_Syntax_Syntax.sigmeta = uu____14158;
                          FStar_Syntax_Syntax.sigattrs = uu____14159;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14174 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14134
                     (FStar_Util.map_option
                        (fun uu____14222  ->
                           match uu____14222 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14253 =
          let uu____14264 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14264 mapper  in
        match uu____14253 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14338 =
              let uu____14349 =
                let uu____14356 =
                  let uu___247_14359 = t  in
                  let uu____14360 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___247_14359.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14360;
                    FStar_Syntax_Syntax.vars =
                      (uu___247_14359.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14356)  in
              (uu____14349, r)  in
            FStar_Pervasives_Native.Some uu____14338
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14407 = lookup_qname env l  in
      match uu____14407 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14426 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14478 = try_lookup_bv env bv  in
      match uu____14478 with
      | FStar_Pervasives_Native.None  ->
          let uu____14493 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14493 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14508 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14509 =
            let uu____14510 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14510  in
          (uu____14508, uu____14509)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14531 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14531 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14597 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14597  in
          let uu____14598 =
            let uu____14607 =
              let uu____14612 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14612)  in
            (uu____14607, r1)  in
          FStar_Pervasives_Native.Some uu____14598
  
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
        let uu____14646 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14646 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14679,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14704 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14704  in
            let uu____14705 =
              let uu____14710 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14710, r1)  in
            FStar_Pervasives_Native.Some uu____14705
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14733 = try_lookup_lid env l  in
      match uu____14733 with
      | FStar_Pervasives_Native.None  ->
          let uu____14760 = name_not_found l  in
          let uu____14765 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14760 uu____14765
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___228_14805  ->
              match uu___228_14805 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14807 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14826 = lookup_qname env lid  in
      match uu____14826 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14835,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14838;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14840;
              FStar_Syntax_Syntax.sigattrs = uu____14841;_},FStar_Pervasives_Native.None
            ),uu____14842)
          ->
          let uu____14891 =
            let uu____14898 =
              let uu____14899 =
                let uu____14902 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14902 t  in
              (uvs, uu____14899)  in
            (uu____14898, q)  in
          FStar_Pervasives_Native.Some uu____14891
      | uu____14915 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14936 = lookup_qname env lid  in
      match uu____14936 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14941,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14944;
              FStar_Syntax_Syntax.sigquals = uu____14945;
              FStar_Syntax_Syntax.sigmeta = uu____14946;
              FStar_Syntax_Syntax.sigattrs = uu____14947;_},FStar_Pervasives_Native.None
            ),uu____14948)
          ->
          let uu____14997 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14997 (uvs, t)
      | uu____15002 ->
          let uu____15003 = name_not_found lid  in
          let uu____15008 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15003 uu____15008
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15027 = lookup_qname env lid  in
      match uu____15027 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15032,uvs,t,uu____15035,uu____15036,uu____15037);
              FStar_Syntax_Syntax.sigrng = uu____15038;
              FStar_Syntax_Syntax.sigquals = uu____15039;
              FStar_Syntax_Syntax.sigmeta = uu____15040;
              FStar_Syntax_Syntax.sigattrs = uu____15041;_},FStar_Pervasives_Native.None
            ),uu____15042)
          ->
          let uu____15095 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15095 (uvs, t)
      | uu____15100 ->
          let uu____15101 = name_not_found lid  in
          let uu____15106 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15101 uu____15106
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15127 = lookup_qname env lid  in
      match uu____15127 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15134,uu____15135,uu____15136,uu____15137,uu____15138,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15140;
              FStar_Syntax_Syntax.sigquals = uu____15141;
              FStar_Syntax_Syntax.sigmeta = uu____15142;
              FStar_Syntax_Syntax.sigattrs = uu____15143;_},uu____15144),uu____15145)
          -> (true, dcs)
      | uu____15206 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15219 = lookup_qname env lid  in
      match uu____15219 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15220,uu____15221,uu____15222,l,uu____15224,uu____15225);
              FStar_Syntax_Syntax.sigrng = uu____15226;
              FStar_Syntax_Syntax.sigquals = uu____15227;
              FStar_Syntax_Syntax.sigmeta = uu____15228;
              FStar_Syntax_Syntax.sigattrs = uu____15229;_},uu____15230),uu____15231)
          -> l
      | uu____15286 ->
          let uu____15287 =
            let uu____15288 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15288  in
          failwith uu____15287
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15337)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15388,lbs),uu____15390)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15412 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15412
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15444 -> FStar_Pervasives_Native.None)
        | uu____15449 -> FStar_Pervasives_Native.None
  
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
        let uu____15479 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15479
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15504),uu____15505) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15554 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15575),uu____15576) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15625 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15646 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15646
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15665 = lookup_qname env ftv  in
      match uu____15665 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15669) ->
          let uu____15714 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15714 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15735,t),r) ->
               let uu____15750 =
                 let uu____15751 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15751 t  in
               FStar_Pervasives_Native.Some uu____15750)
      | uu____15752 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15763 = try_lookup_effect_lid env ftv  in
      match uu____15763 with
      | FStar_Pervasives_Native.None  ->
          let uu____15766 = name_not_found ftv  in
          let uu____15771 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15766 uu____15771
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
        let uu____15794 = lookup_qname env lid0  in
        match uu____15794 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15805);
                FStar_Syntax_Syntax.sigrng = uu____15806;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15808;
                FStar_Syntax_Syntax.sigattrs = uu____15809;_},FStar_Pervasives_Native.None
              ),uu____15810)
            ->
            let lid1 =
              let uu____15864 =
                let uu____15865 = FStar_Ident.range_of_lid lid  in
                let uu____15866 =
                  let uu____15867 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____15867  in
                FStar_Range.set_use_range uu____15865 uu____15866  in
              FStar_Ident.set_lid_range lid uu____15864  in
            let uu____15868 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___229_15872  ->
                      match uu___229_15872 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____15873 -> false))
               in
            if uu____15868
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15887 =
                      let uu____15888 =
                        let uu____15889 = get_range env  in
                        FStar_Range.string_of_range uu____15889  in
                      let uu____15890 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____15891 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15888 uu____15890 uu____15891
                       in
                    failwith uu____15887)
                  in
               match (binders, univs1) with
               | ([],uu____15908) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____15933,uu____15934::uu____15935::uu____15936) ->
                   let uu____15957 =
                     let uu____15958 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____15959 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____15958 uu____15959
                      in
                   failwith uu____15957
               | uu____15966 ->
                   let uu____15981 =
                     let uu____15986 =
                       let uu____15987 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____15987)  in
                     inst_tscheme_with uu____15986 insts  in
                   (match uu____15981 with
                    | (uu____16000,t) ->
                        let t1 =
                          let uu____16003 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16003 t  in
                        let uu____16004 =
                          let uu____16005 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16005.FStar_Syntax_Syntax.n  in
                        (match uu____16004 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16040 -> failwith "Impossible")))
        | uu____16047 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16070 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16070 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16083,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16090 = find1 l2  in
            (match uu____16090 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16097 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16097 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16101 = find1 l  in
            (match uu____16101 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16106 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16106
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16120 = lookup_qname env l1  in
      match uu____16120 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16123;
              FStar_Syntax_Syntax.sigrng = uu____16124;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16126;
              FStar_Syntax_Syntax.sigattrs = uu____16127;_},uu____16128),uu____16129)
          -> q
      | uu____16180 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16201 =
          let uu____16202 =
            let uu____16203 = FStar_Util.string_of_int i  in
            let uu____16204 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16203 uu____16204
             in
          failwith uu____16202  in
        let uu____16205 = lookup_datacon env lid  in
        match uu____16205 with
        | (uu____16210,t) ->
            let uu____16212 =
              let uu____16213 = FStar_Syntax_Subst.compress t  in
              uu____16213.FStar_Syntax_Syntax.n  in
            (match uu____16212 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16217) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16258 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16258
                      FStar_Pervasives_Native.fst)
             | uu____16269 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16280 = lookup_qname env l  in
      match uu____16280 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16281,uu____16282,uu____16283);
              FStar_Syntax_Syntax.sigrng = uu____16284;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16286;
              FStar_Syntax_Syntax.sigattrs = uu____16287;_},uu____16288),uu____16289)
          ->
          FStar_Util.for_some
            (fun uu___230_16342  ->
               match uu___230_16342 with
               | FStar_Syntax_Syntax.Projector uu____16343 -> true
               | uu____16348 -> false) quals
      | uu____16349 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16360 = lookup_qname env lid  in
      match uu____16360 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16361,uu____16362,uu____16363,uu____16364,uu____16365,uu____16366);
              FStar_Syntax_Syntax.sigrng = uu____16367;
              FStar_Syntax_Syntax.sigquals = uu____16368;
              FStar_Syntax_Syntax.sigmeta = uu____16369;
              FStar_Syntax_Syntax.sigattrs = uu____16370;_},uu____16371),uu____16372)
          -> true
      | uu____16427 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16438 = lookup_qname env lid  in
      match uu____16438 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16439,uu____16440,uu____16441,uu____16442,uu____16443,uu____16444);
              FStar_Syntax_Syntax.sigrng = uu____16445;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16447;
              FStar_Syntax_Syntax.sigattrs = uu____16448;_},uu____16449),uu____16450)
          ->
          FStar_Util.for_some
            (fun uu___231_16511  ->
               match uu___231_16511 with
               | FStar_Syntax_Syntax.RecordType uu____16512 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16521 -> true
               | uu____16530 -> false) quals
      | uu____16531 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16537,uu____16538);
            FStar_Syntax_Syntax.sigrng = uu____16539;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16541;
            FStar_Syntax_Syntax.sigattrs = uu____16542;_},uu____16543),uu____16544)
        ->
        FStar_Util.for_some
          (fun uu___232_16601  ->
             match uu___232_16601 with
             | FStar_Syntax_Syntax.Action uu____16602 -> true
             | uu____16603 -> false) quals
    | uu____16604 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16615 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16615
  
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
      let uu____16629 =
        let uu____16630 = FStar_Syntax_Util.un_uinst head1  in
        uu____16630.FStar_Syntax_Syntax.n  in
      match uu____16629 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16634 ->
               true
           | uu____16635 -> false)
      | uu____16636 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16647 = lookup_qname env l  in
      match uu____16647 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16649),uu____16650) ->
          FStar_Util.for_some
            (fun uu___233_16698  ->
               match uu___233_16698 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16699 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16700 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16771 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16787) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16804 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16811 ->
                 FStar_Pervasives_Native.Some true
             | uu____16828 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16829 =
        let uu____16832 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16832 mapper  in
      match uu____16829 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____16882 = lookup_qname env lid  in
      match uu____16882 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16883,uu____16884,tps,uu____16886,uu____16887,uu____16888);
              FStar_Syntax_Syntax.sigrng = uu____16889;
              FStar_Syntax_Syntax.sigquals = uu____16890;
              FStar_Syntax_Syntax.sigmeta = uu____16891;
              FStar_Syntax_Syntax.sigattrs = uu____16892;_},uu____16893),uu____16894)
          -> FStar_List.length tps
      | uu____16959 ->
          let uu____16960 = name_not_found lid  in
          let uu____16965 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____16960 uu____16965
  
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
           (fun uu____17009  ->
              match uu____17009 with
              | (d,uu____17017) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17032 = effect_decl_opt env l  in
      match uu____17032 with
      | FStar_Pervasives_Native.None  ->
          let uu____17047 = name_not_found l  in
          let uu____17052 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17047 uu____17052
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17074  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17093  ->
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
        let uu____17124 = FStar_Ident.lid_equals l1 l2  in
        if uu____17124
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17132 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17132
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17140 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17193  ->
                        match uu____17193 with
                        | (m1,m2,uu____17206,uu____17207,uu____17208) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17140 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17225 =
                    let uu____17230 =
                      let uu____17231 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17232 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17231
                        uu____17232
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17230)
                     in
                  FStar_Errors.raise_error uu____17225 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17239,uu____17240,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17273 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17273
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
  'Auu____17289 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17289)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17318 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17344  ->
                match uu____17344 with
                | (d,uu____17350) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17318 with
      | FStar_Pervasives_Native.None  ->
          let uu____17361 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17361
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17374 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17374 with
           | (uu____17389,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17407)::(wp,uu____17409)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17465 -> failwith "Impossible"))
  
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
          let uu____17520 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17520
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17522 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17522
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
                  let uu____17530 = get_range env  in
                  let uu____17531 =
                    let uu____17538 =
                      let uu____17539 =
                        let uu____17556 =
                          let uu____17567 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17567]  in
                        (null_wp, uu____17556)  in
                      FStar_Syntax_Syntax.Tm_app uu____17539  in
                    FStar_Syntax_Syntax.mk uu____17538  in
                  uu____17531 FStar_Pervasives_Native.None uu____17530  in
                let uu____17607 =
                  let uu____17608 =
                    let uu____17619 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17619]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17608;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17607))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___248_17656 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___248_17656.order);
              joins = (uu___248_17656.joins)
            }  in
          let uu___249_17665 = env  in
          {
            solver = (uu___249_17665.solver);
            range = (uu___249_17665.range);
            curmodule = (uu___249_17665.curmodule);
            gamma = (uu___249_17665.gamma);
            gamma_sig = (uu___249_17665.gamma_sig);
            gamma_cache = (uu___249_17665.gamma_cache);
            modules = (uu___249_17665.modules);
            expected_typ = (uu___249_17665.expected_typ);
            sigtab = (uu___249_17665.sigtab);
            attrtab = (uu___249_17665.attrtab);
            is_pattern = (uu___249_17665.is_pattern);
            instantiate_imp = (uu___249_17665.instantiate_imp);
            effects;
            generalize = (uu___249_17665.generalize);
            letrecs = (uu___249_17665.letrecs);
            top_level = (uu___249_17665.top_level);
            check_uvars = (uu___249_17665.check_uvars);
            use_eq = (uu___249_17665.use_eq);
            is_iface = (uu___249_17665.is_iface);
            admit = (uu___249_17665.admit);
            lax = (uu___249_17665.lax);
            lax_universes = (uu___249_17665.lax_universes);
            phase1 = (uu___249_17665.phase1);
            failhard = (uu___249_17665.failhard);
            nosynth = (uu___249_17665.nosynth);
            uvar_subtyping = (uu___249_17665.uvar_subtyping);
            tc_term = (uu___249_17665.tc_term);
            type_of = (uu___249_17665.type_of);
            universe_of = (uu___249_17665.universe_of);
            check_type_of = (uu___249_17665.check_type_of);
            use_bv_sorts = (uu___249_17665.use_bv_sorts);
            qtbl_name_and_index = (uu___249_17665.qtbl_name_and_index);
            normalized_eff_names = (uu___249_17665.normalized_eff_names);
            proof_ns = (uu___249_17665.proof_ns);
            synth_hook = (uu___249_17665.synth_hook);
            splice = (uu___249_17665.splice);
            is_native_tactic = (uu___249_17665.is_native_tactic);
            identifier_info = (uu___249_17665.identifier_info);
            tc_hooks = (uu___249_17665.tc_hooks);
            dsenv = (uu___249_17665.dsenv);
            dep_graph = (uu___249_17665.dep_graph);
            nbe = (uu___249_17665.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17695 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17695  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____17853 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____17854 = l1 u t wp e  in
                                l2 u t uu____17853 uu____17854))
                | uu____17855 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____17927 = inst_tscheme_with lift_t [u]  in
            match uu____17927 with
            | (uu____17934,lift_t1) ->
                let uu____17936 =
                  let uu____17943 =
                    let uu____17944 =
                      let uu____17961 =
                        let uu____17972 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17981 =
                          let uu____17992 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____17992]  in
                        uu____17972 :: uu____17981  in
                      (lift_t1, uu____17961)  in
                    FStar_Syntax_Syntax.Tm_app uu____17944  in
                  FStar_Syntax_Syntax.mk uu____17943  in
                uu____17936 FStar_Pervasives_Native.None
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
            let uu____18104 = inst_tscheme_with lift_t [u]  in
            match uu____18104 with
            | (uu____18111,lift_t1) ->
                let uu____18113 =
                  let uu____18120 =
                    let uu____18121 =
                      let uu____18138 =
                        let uu____18149 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18158 =
                          let uu____18169 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18178 =
                            let uu____18189 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18189]  in
                          uu____18169 :: uu____18178  in
                        uu____18149 :: uu____18158  in
                      (lift_t1, uu____18138)  in
                    FStar_Syntax_Syntax.Tm_app uu____18121  in
                  FStar_Syntax_Syntax.mk uu____18120  in
                uu____18113 FStar_Pervasives_Native.None
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
              let uu____18291 =
                let uu____18292 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18292
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18291  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18296 =
              let uu____18297 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18297  in
            let uu____18298 =
              let uu____18299 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18325 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18325)
                 in
              FStar_Util.dflt "none" uu____18299  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18296
              uu____18298
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18351  ->
                    match uu____18351 with
                    | (e,uu____18359) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18382 =
            match uu____18382 with
            | (i,j) ->
                let uu____18393 = FStar_Ident.lid_equals i j  in
                if uu____18393
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
              let uu____18425 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18435 = FStar_Ident.lid_equals i k  in
                        if uu____18435
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18446 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18446
                                  then []
                                  else
                                    (let uu____18450 =
                                       let uu____18459 =
                                         find_edge order1 (i, k)  in
                                       let uu____18462 =
                                         find_edge order1 (k, j)  in
                                       (uu____18459, uu____18462)  in
                                     match uu____18450 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18477 =
                                           compose_edges e1 e2  in
                                         [uu____18477]
                                     | uu____18478 -> [])))))
                 in
              FStar_List.append order1 uu____18425  in
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
                   let uu____18508 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18510 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18510
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18508
                   then
                     let uu____18515 =
                       let uu____18520 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18520)
                        in
                     let uu____18521 = get_range env  in
                     FStar_Errors.raise_error uu____18515 uu____18521
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18598 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18598
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18647 =
                                              let uu____18656 =
                                                find_edge order2 (i, k)  in
                                              let uu____18659 =
                                                find_edge order2 (j, k)  in
                                              (uu____18656, uu____18659)  in
                                            match uu____18647 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18701,uu____18702)
                                                     ->
                                                     let uu____18709 =
                                                       let uu____18714 =
                                                         let uu____18715 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18715
                                                          in
                                                       let uu____18718 =
                                                         let uu____18719 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18719
                                                          in
                                                       (uu____18714,
                                                         uu____18718)
                                                        in
                                                     (match uu____18709 with
                                                      | (true ,true ) ->
                                                          let uu____18730 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18730
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
                                            | uu____18755 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___250_18828 = env.effects  in
              { decls = (uu___250_18828.decls); order = order2; joins }  in
            let uu___251_18829 = env  in
            {
              solver = (uu___251_18829.solver);
              range = (uu___251_18829.range);
              curmodule = (uu___251_18829.curmodule);
              gamma = (uu___251_18829.gamma);
              gamma_sig = (uu___251_18829.gamma_sig);
              gamma_cache = (uu___251_18829.gamma_cache);
              modules = (uu___251_18829.modules);
              expected_typ = (uu___251_18829.expected_typ);
              sigtab = (uu___251_18829.sigtab);
              attrtab = (uu___251_18829.attrtab);
              is_pattern = (uu___251_18829.is_pattern);
              instantiate_imp = (uu___251_18829.instantiate_imp);
              effects;
              generalize = (uu___251_18829.generalize);
              letrecs = (uu___251_18829.letrecs);
              top_level = (uu___251_18829.top_level);
              check_uvars = (uu___251_18829.check_uvars);
              use_eq = (uu___251_18829.use_eq);
              is_iface = (uu___251_18829.is_iface);
              admit = (uu___251_18829.admit);
              lax = (uu___251_18829.lax);
              lax_universes = (uu___251_18829.lax_universes);
              phase1 = (uu___251_18829.phase1);
              failhard = (uu___251_18829.failhard);
              nosynth = (uu___251_18829.nosynth);
              uvar_subtyping = (uu___251_18829.uvar_subtyping);
              tc_term = (uu___251_18829.tc_term);
              type_of = (uu___251_18829.type_of);
              universe_of = (uu___251_18829.universe_of);
              check_type_of = (uu___251_18829.check_type_of);
              use_bv_sorts = (uu___251_18829.use_bv_sorts);
              qtbl_name_and_index = (uu___251_18829.qtbl_name_and_index);
              normalized_eff_names = (uu___251_18829.normalized_eff_names);
              proof_ns = (uu___251_18829.proof_ns);
              synth_hook = (uu___251_18829.synth_hook);
              splice = (uu___251_18829.splice);
              is_native_tactic = (uu___251_18829.is_native_tactic);
              identifier_info = (uu___251_18829.identifier_info);
              tc_hooks = (uu___251_18829.tc_hooks);
              dsenv = (uu___251_18829.dsenv);
              dep_graph = (uu___251_18829.dep_graph);
              nbe = (uu___251_18829.nbe)
            }))
      | uu____18830 -> env
  
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
        | uu____18858 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____18870 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____18870 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____18887 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____18887 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18909 =
                     let uu____18914 =
                       let uu____18915 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____18922 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____18931 =
                         let uu____18932 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____18932  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18915 uu____18922 uu____18931
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18914)
                      in
                   FStar_Errors.raise_error uu____18909
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____18937 =
                     let uu____18948 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____18948 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____18985  ->
                        fun uu____18986  ->
                          match (uu____18985, uu____18986) with
                          | ((x,uu____19016),(t,uu____19018)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____18937
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19049 =
                     let uu___252_19050 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___252_19050.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___252_19050.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___252_19050.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___252_19050.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19049
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____19061 .
    'Auu____19061 ->
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
          let uu____19091 = effect_decl_opt env effect_name  in
          match uu____19091 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____19130 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19153 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____19190 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____19190
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____19191 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19191
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____19205 =
                     let uu____19208 = get_range env  in
                     let uu____19209 =
                       let uu____19216 =
                         let uu____19217 =
                           let uu____19234 =
                             let uu____19245 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____19245; wp]  in
                           (repr, uu____19234)  in
                         FStar_Syntax_Syntax.Tm_app uu____19217  in
                       FStar_Syntax_Syntax.mk uu____19216  in
                     uu____19209 FStar_Pervasives_Native.None uu____19208  in
                   FStar_Pervasives_Native.Some uu____19205)
  
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
      | uu____19360 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19371 =
        let uu____19372 = FStar_Syntax_Subst.compress t  in
        uu____19372.FStar_Syntax_Syntax.n  in
      match uu____19371 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19375,c) ->
          is_reifiable_comp env c
      | uu____19397 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____19415 =
           let uu____19416 = is_reifiable_effect env l  in
           Prims.op_Negation uu____19416  in
         if uu____19415
         then
           let uu____19417 =
             let uu____19422 =
               let uu____19423 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19423
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19422)  in
           let uu____19424 = get_range env  in
           FStar_Errors.raise_error uu____19417 uu____19424
         else ());
        (let uu____19426 = effect_repr_aux true env c u_c  in
         match uu____19426 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___253_19458 = env  in
        {
          solver = (uu___253_19458.solver);
          range = (uu___253_19458.range);
          curmodule = (uu___253_19458.curmodule);
          gamma = (uu___253_19458.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___253_19458.gamma_cache);
          modules = (uu___253_19458.modules);
          expected_typ = (uu___253_19458.expected_typ);
          sigtab = (uu___253_19458.sigtab);
          attrtab = (uu___253_19458.attrtab);
          is_pattern = (uu___253_19458.is_pattern);
          instantiate_imp = (uu___253_19458.instantiate_imp);
          effects = (uu___253_19458.effects);
          generalize = (uu___253_19458.generalize);
          letrecs = (uu___253_19458.letrecs);
          top_level = (uu___253_19458.top_level);
          check_uvars = (uu___253_19458.check_uvars);
          use_eq = (uu___253_19458.use_eq);
          is_iface = (uu___253_19458.is_iface);
          admit = (uu___253_19458.admit);
          lax = (uu___253_19458.lax);
          lax_universes = (uu___253_19458.lax_universes);
          phase1 = (uu___253_19458.phase1);
          failhard = (uu___253_19458.failhard);
          nosynth = (uu___253_19458.nosynth);
          uvar_subtyping = (uu___253_19458.uvar_subtyping);
          tc_term = (uu___253_19458.tc_term);
          type_of = (uu___253_19458.type_of);
          universe_of = (uu___253_19458.universe_of);
          check_type_of = (uu___253_19458.check_type_of);
          use_bv_sorts = (uu___253_19458.use_bv_sorts);
          qtbl_name_and_index = (uu___253_19458.qtbl_name_and_index);
          normalized_eff_names = (uu___253_19458.normalized_eff_names);
          proof_ns = (uu___253_19458.proof_ns);
          synth_hook = (uu___253_19458.synth_hook);
          splice = (uu___253_19458.splice);
          is_native_tactic = (uu___253_19458.is_native_tactic);
          identifier_info = (uu___253_19458.identifier_info);
          tc_hooks = (uu___253_19458.tc_hooks);
          dsenv = (uu___253_19458.dsenv);
          dep_graph = (uu___253_19458.dep_graph);
          nbe = (uu___253_19458.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___254_19471 = env  in
      {
        solver = (uu___254_19471.solver);
        range = (uu___254_19471.range);
        curmodule = (uu___254_19471.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___254_19471.gamma_sig);
        gamma_cache = (uu___254_19471.gamma_cache);
        modules = (uu___254_19471.modules);
        expected_typ = (uu___254_19471.expected_typ);
        sigtab = (uu___254_19471.sigtab);
        attrtab = (uu___254_19471.attrtab);
        is_pattern = (uu___254_19471.is_pattern);
        instantiate_imp = (uu___254_19471.instantiate_imp);
        effects = (uu___254_19471.effects);
        generalize = (uu___254_19471.generalize);
        letrecs = (uu___254_19471.letrecs);
        top_level = (uu___254_19471.top_level);
        check_uvars = (uu___254_19471.check_uvars);
        use_eq = (uu___254_19471.use_eq);
        is_iface = (uu___254_19471.is_iface);
        admit = (uu___254_19471.admit);
        lax = (uu___254_19471.lax);
        lax_universes = (uu___254_19471.lax_universes);
        phase1 = (uu___254_19471.phase1);
        failhard = (uu___254_19471.failhard);
        nosynth = (uu___254_19471.nosynth);
        uvar_subtyping = (uu___254_19471.uvar_subtyping);
        tc_term = (uu___254_19471.tc_term);
        type_of = (uu___254_19471.type_of);
        universe_of = (uu___254_19471.universe_of);
        check_type_of = (uu___254_19471.check_type_of);
        use_bv_sorts = (uu___254_19471.use_bv_sorts);
        qtbl_name_and_index = (uu___254_19471.qtbl_name_and_index);
        normalized_eff_names = (uu___254_19471.normalized_eff_names);
        proof_ns = (uu___254_19471.proof_ns);
        synth_hook = (uu___254_19471.synth_hook);
        splice = (uu___254_19471.splice);
        is_native_tactic = (uu___254_19471.is_native_tactic);
        identifier_info = (uu___254_19471.identifier_info);
        tc_hooks = (uu___254_19471.tc_hooks);
        dsenv = (uu___254_19471.dsenv);
        dep_graph = (uu___254_19471.dep_graph);
        nbe = (uu___254_19471.nbe)
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
            (let uu___255_19526 = env  in
             {
               solver = (uu___255_19526.solver);
               range = (uu___255_19526.range);
               curmodule = (uu___255_19526.curmodule);
               gamma = rest;
               gamma_sig = (uu___255_19526.gamma_sig);
               gamma_cache = (uu___255_19526.gamma_cache);
               modules = (uu___255_19526.modules);
               expected_typ = (uu___255_19526.expected_typ);
               sigtab = (uu___255_19526.sigtab);
               attrtab = (uu___255_19526.attrtab);
               is_pattern = (uu___255_19526.is_pattern);
               instantiate_imp = (uu___255_19526.instantiate_imp);
               effects = (uu___255_19526.effects);
               generalize = (uu___255_19526.generalize);
               letrecs = (uu___255_19526.letrecs);
               top_level = (uu___255_19526.top_level);
               check_uvars = (uu___255_19526.check_uvars);
               use_eq = (uu___255_19526.use_eq);
               is_iface = (uu___255_19526.is_iface);
               admit = (uu___255_19526.admit);
               lax = (uu___255_19526.lax);
               lax_universes = (uu___255_19526.lax_universes);
               phase1 = (uu___255_19526.phase1);
               failhard = (uu___255_19526.failhard);
               nosynth = (uu___255_19526.nosynth);
               uvar_subtyping = (uu___255_19526.uvar_subtyping);
               tc_term = (uu___255_19526.tc_term);
               type_of = (uu___255_19526.type_of);
               universe_of = (uu___255_19526.universe_of);
               check_type_of = (uu___255_19526.check_type_of);
               use_bv_sorts = (uu___255_19526.use_bv_sorts);
               qtbl_name_and_index = (uu___255_19526.qtbl_name_and_index);
               normalized_eff_names = (uu___255_19526.normalized_eff_names);
               proof_ns = (uu___255_19526.proof_ns);
               synth_hook = (uu___255_19526.synth_hook);
               splice = (uu___255_19526.splice);
               is_native_tactic = (uu___255_19526.is_native_tactic);
               identifier_info = (uu___255_19526.identifier_info);
               tc_hooks = (uu___255_19526.tc_hooks);
               dsenv = (uu___255_19526.dsenv);
               dep_graph = (uu___255_19526.dep_graph);
               nbe = (uu___255_19526.nbe)
             }))
    | uu____19527 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19555  ->
             match uu____19555 with | (x,uu____19563) -> push_bv env1 x) env
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
            let uu___256_19597 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___256_19597.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___256_19597.FStar_Syntax_Syntax.index);
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
      (let uu___257_19637 = env  in
       {
         solver = (uu___257_19637.solver);
         range = (uu___257_19637.range);
         curmodule = (uu___257_19637.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_19637.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___257_19637.sigtab);
         attrtab = (uu___257_19637.attrtab);
         is_pattern = (uu___257_19637.is_pattern);
         instantiate_imp = (uu___257_19637.instantiate_imp);
         effects = (uu___257_19637.effects);
         generalize = (uu___257_19637.generalize);
         letrecs = (uu___257_19637.letrecs);
         top_level = (uu___257_19637.top_level);
         check_uvars = (uu___257_19637.check_uvars);
         use_eq = (uu___257_19637.use_eq);
         is_iface = (uu___257_19637.is_iface);
         admit = (uu___257_19637.admit);
         lax = (uu___257_19637.lax);
         lax_universes = (uu___257_19637.lax_universes);
         phase1 = (uu___257_19637.phase1);
         failhard = (uu___257_19637.failhard);
         nosynth = (uu___257_19637.nosynth);
         uvar_subtyping = (uu___257_19637.uvar_subtyping);
         tc_term = (uu___257_19637.tc_term);
         type_of = (uu___257_19637.type_of);
         universe_of = (uu___257_19637.universe_of);
         check_type_of = (uu___257_19637.check_type_of);
         use_bv_sorts = (uu___257_19637.use_bv_sorts);
         qtbl_name_and_index = (uu___257_19637.qtbl_name_and_index);
         normalized_eff_names = (uu___257_19637.normalized_eff_names);
         proof_ns = (uu___257_19637.proof_ns);
         synth_hook = (uu___257_19637.synth_hook);
         splice = (uu___257_19637.splice);
         is_native_tactic = (uu___257_19637.is_native_tactic);
         identifier_info = (uu___257_19637.identifier_info);
         tc_hooks = (uu___257_19637.tc_hooks);
         dsenv = (uu___257_19637.dsenv);
         dep_graph = (uu___257_19637.dep_graph);
         nbe = (uu___257_19637.nbe)
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
        let uu____19679 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19679 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19707 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19707)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___258_19722 = env  in
      {
        solver = (uu___258_19722.solver);
        range = (uu___258_19722.range);
        curmodule = (uu___258_19722.curmodule);
        gamma = (uu___258_19722.gamma);
        gamma_sig = (uu___258_19722.gamma_sig);
        gamma_cache = (uu___258_19722.gamma_cache);
        modules = (uu___258_19722.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___258_19722.sigtab);
        attrtab = (uu___258_19722.attrtab);
        is_pattern = (uu___258_19722.is_pattern);
        instantiate_imp = (uu___258_19722.instantiate_imp);
        effects = (uu___258_19722.effects);
        generalize = (uu___258_19722.generalize);
        letrecs = (uu___258_19722.letrecs);
        top_level = (uu___258_19722.top_level);
        check_uvars = (uu___258_19722.check_uvars);
        use_eq = false;
        is_iface = (uu___258_19722.is_iface);
        admit = (uu___258_19722.admit);
        lax = (uu___258_19722.lax);
        lax_universes = (uu___258_19722.lax_universes);
        phase1 = (uu___258_19722.phase1);
        failhard = (uu___258_19722.failhard);
        nosynth = (uu___258_19722.nosynth);
        uvar_subtyping = (uu___258_19722.uvar_subtyping);
        tc_term = (uu___258_19722.tc_term);
        type_of = (uu___258_19722.type_of);
        universe_of = (uu___258_19722.universe_of);
        check_type_of = (uu___258_19722.check_type_of);
        use_bv_sorts = (uu___258_19722.use_bv_sorts);
        qtbl_name_and_index = (uu___258_19722.qtbl_name_and_index);
        normalized_eff_names = (uu___258_19722.normalized_eff_names);
        proof_ns = (uu___258_19722.proof_ns);
        synth_hook = (uu___258_19722.synth_hook);
        splice = (uu___258_19722.splice);
        is_native_tactic = (uu___258_19722.is_native_tactic);
        identifier_info = (uu___258_19722.identifier_info);
        tc_hooks = (uu___258_19722.tc_hooks);
        dsenv = (uu___258_19722.dsenv);
        dep_graph = (uu___258_19722.dep_graph);
        nbe = (uu___258_19722.nbe)
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
    let uu____19750 = expected_typ env_  in
    ((let uu___259_19756 = env_  in
      {
        solver = (uu___259_19756.solver);
        range = (uu___259_19756.range);
        curmodule = (uu___259_19756.curmodule);
        gamma = (uu___259_19756.gamma);
        gamma_sig = (uu___259_19756.gamma_sig);
        gamma_cache = (uu___259_19756.gamma_cache);
        modules = (uu___259_19756.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___259_19756.sigtab);
        attrtab = (uu___259_19756.attrtab);
        is_pattern = (uu___259_19756.is_pattern);
        instantiate_imp = (uu___259_19756.instantiate_imp);
        effects = (uu___259_19756.effects);
        generalize = (uu___259_19756.generalize);
        letrecs = (uu___259_19756.letrecs);
        top_level = (uu___259_19756.top_level);
        check_uvars = (uu___259_19756.check_uvars);
        use_eq = false;
        is_iface = (uu___259_19756.is_iface);
        admit = (uu___259_19756.admit);
        lax = (uu___259_19756.lax);
        lax_universes = (uu___259_19756.lax_universes);
        phase1 = (uu___259_19756.phase1);
        failhard = (uu___259_19756.failhard);
        nosynth = (uu___259_19756.nosynth);
        uvar_subtyping = (uu___259_19756.uvar_subtyping);
        tc_term = (uu___259_19756.tc_term);
        type_of = (uu___259_19756.type_of);
        universe_of = (uu___259_19756.universe_of);
        check_type_of = (uu___259_19756.check_type_of);
        use_bv_sorts = (uu___259_19756.use_bv_sorts);
        qtbl_name_and_index = (uu___259_19756.qtbl_name_and_index);
        normalized_eff_names = (uu___259_19756.normalized_eff_names);
        proof_ns = (uu___259_19756.proof_ns);
        synth_hook = (uu___259_19756.synth_hook);
        splice = (uu___259_19756.splice);
        is_native_tactic = (uu___259_19756.is_native_tactic);
        identifier_info = (uu___259_19756.identifier_info);
        tc_hooks = (uu___259_19756.tc_hooks);
        dsenv = (uu___259_19756.dsenv);
        dep_graph = (uu___259_19756.dep_graph);
        nbe = (uu___259_19756.nbe)
      }), uu____19750)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19766 =
      let uu____19769 = FStar_Ident.id_of_text ""  in [uu____19769]  in
    FStar_Ident.lid_of_ids uu____19766  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19775 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19775
        then
          let uu____19778 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19778 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___260_19805 = env  in
       {
         solver = (uu___260_19805.solver);
         range = (uu___260_19805.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___260_19805.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___260_19805.expected_typ);
         sigtab = (uu___260_19805.sigtab);
         attrtab = (uu___260_19805.attrtab);
         is_pattern = (uu___260_19805.is_pattern);
         instantiate_imp = (uu___260_19805.instantiate_imp);
         effects = (uu___260_19805.effects);
         generalize = (uu___260_19805.generalize);
         letrecs = (uu___260_19805.letrecs);
         top_level = (uu___260_19805.top_level);
         check_uvars = (uu___260_19805.check_uvars);
         use_eq = (uu___260_19805.use_eq);
         is_iface = (uu___260_19805.is_iface);
         admit = (uu___260_19805.admit);
         lax = (uu___260_19805.lax);
         lax_universes = (uu___260_19805.lax_universes);
         phase1 = (uu___260_19805.phase1);
         failhard = (uu___260_19805.failhard);
         nosynth = (uu___260_19805.nosynth);
         uvar_subtyping = (uu___260_19805.uvar_subtyping);
         tc_term = (uu___260_19805.tc_term);
         type_of = (uu___260_19805.type_of);
         universe_of = (uu___260_19805.universe_of);
         check_type_of = (uu___260_19805.check_type_of);
         use_bv_sorts = (uu___260_19805.use_bv_sorts);
         qtbl_name_and_index = (uu___260_19805.qtbl_name_and_index);
         normalized_eff_names = (uu___260_19805.normalized_eff_names);
         proof_ns = (uu___260_19805.proof_ns);
         synth_hook = (uu___260_19805.synth_hook);
         splice = (uu___260_19805.splice);
         is_native_tactic = (uu___260_19805.is_native_tactic);
         identifier_info = (uu___260_19805.identifier_info);
         tc_hooks = (uu___260_19805.tc_hooks);
         dsenv = (uu___260_19805.dsenv);
         dep_graph = (uu___260_19805.dep_graph);
         nbe = (uu___260_19805.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19856)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19860,(uu____19861,t)))::tl1
          ->
          let uu____19882 =
            let uu____19885 = FStar_Syntax_Free.uvars t  in
            ext out uu____19885  in
          aux uu____19882 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19888;
            FStar_Syntax_Syntax.index = uu____19889;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19896 =
            let uu____19899 = FStar_Syntax_Free.uvars t  in
            ext out uu____19899  in
          aux uu____19896 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19956)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19960,(uu____19961,t)))::tl1
          ->
          let uu____19982 =
            let uu____19985 = FStar_Syntax_Free.univs t  in
            ext out uu____19985  in
          aux uu____19982 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19988;
            FStar_Syntax_Syntax.index = uu____19989;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19996 =
            let uu____19999 = FStar_Syntax_Free.univs t  in
            ext out uu____19999  in
          aux uu____19996 tl1
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
          let uu____20060 = FStar_Util.set_add uname out  in
          aux uu____20060 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20063,(uu____20064,t)))::tl1
          ->
          let uu____20085 =
            let uu____20088 = FStar_Syntax_Free.univnames t  in
            ext out uu____20088  in
          aux uu____20085 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20091;
            FStar_Syntax_Syntax.index = uu____20092;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20099 =
            let uu____20102 = FStar_Syntax_Free.univnames t  in
            ext out uu____20102  in
          aux uu____20099 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___234_20122  ->
            match uu___234_20122 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20126 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20139 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20149 =
      let uu____20158 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20158
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20149 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20202 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___235_20212  ->
              match uu___235_20212 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20214 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20214
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20217) ->
                  let uu____20234 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20234))
       in
    FStar_All.pipe_right uu____20202 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___236_20241  ->
    match uu___236_20241 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20243 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20243
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20263  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20305) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20324,uu____20325) -> false  in
      let uu____20334 =
        FStar_List.tryFind
          (fun uu____20352  ->
             match uu____20352 with | (p,uu____20360) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20334 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20371,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20393 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20393
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___261_20411 = e  in
        {
          solver = (uu___261_20411.solver);
          range = (uu___261_20411.range);
          curmodule = (uu___261_20411.curmodule);
          gamma = (uu___261_20411.gamma);
          gamma_sig = (uu___261_20411.gamma_sig);
          gamma_cache = (uu___261_20411.gamma_cache);
          modules = (uu___261_20411.modules);
          expected_typ = (uu___261_20411.expected_typ);
          sigtab = (uu___261_20411.sigtab);
          attrtab = (uu___261_20411.attrtab);
          is_pattern = (uu___261_20411.is_pattern);
          instantiate_imp = (uu___261_20411.instantiate_imp);
          effects = (uu___261_20411.effects);
          generalize = (uu___261_20411.generalize);
          letrecs = (uu___261_20411.letrecs);
          top_level = (uu___261_20411.top_level);
          check_uvars = (uu___261_20411.check_uvars);
          use_eq = (uu___261_20411.use_eq);
          is_iface = (uu___261_20411.is_iface);
          admit = (uu___261_20411.admit);
          lax = (uu___261_20411.lax);
          lax_universes = (uu___261_20411.lax_universes);
          phase1 = (uu___261_20411.phase1);
          failhard = (uu___261_20411.failhard);
          nosynth = (uu___261_20411.nosynth);
          uvar_subtyping = (uu___261_20411.uvar_subtyping);
          tc_term = (uu___261_20411.tc_term);
          type_of = (uu___261_20411.type_of);
          universe_of = (uu___261_20411.universe_of);
          check_type_of = (uu___261_20411.check_type_of);
          use_bv_sorts = (uu___261_20411.use_bv_sorts);
          qtbl_name_and_index = (uu___261_20411.qtbl_name_and_index);
          normalized_eff_names = (uu___261_20411.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___261_20411.synth_hook);
          splice = (uu___261_20411.splice);
          is_native_tactic = (uu___261_20411.is_native_tactic);
          identifier_info = (uu___261_20411.identifier_info);
          tc_hooks = (uu___261_20411.tc_hooks);
          dsenv = (uu___261_20411.dsenv);
          dep_graph = (uu___261_20411.dep_graph);
          nbe = (uu___261_20411.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___262_20451 = e  in
      {
        solver = (uu___262_20451.solver);
        range = (uu___262_20451.range);
        curmodule = (uu___262_20451.curmodule);
        gamma = (uu___262_20451.gamma);
        gamma_sig = (uu___262_20451.gamma_sig);
        gamma_cache = (uu___262_20451.gamma_cache);
        modules = (uu___262_20451.modules);
        expected_typ = (uu___262_20451.expected_typ);
        sigtab = (uu___262_20451.sigtab);
        attrtab = (uu___262_20451.attrtab);
        is_pattern = (uu___262_20451.is_pattern);
        instantiate_imp = (uu___262_20451.instantiate_imp);
        effects = (uu___262_20451.effects);
        generalize = (uu___262_20451.generalize);
        letrecs = (uu___262_20451.letrecs);
        top_level = (uu___262_20451.top_level);
        check_uvars = (uu___262_20451.check_uvars);
        use_eq = (uu___262_20451.use_eq);
        is_iface = (uu___262_20451.is_iface);
        admit = (uu___262_20451.admit);
        lax = (uu___262_20451.lax);
        lax_universes = (uu___262_20451.lax_universes);
        phase1 = (uu___262_20451.phase1);
        failhard = (uu___262_20451.failhard);
        nosynth = (uu___262_20451.nosynth);
        uvar_subtyping = (uu___262_20451.uvar_subtyping);
        tc_term = (uu___262_20451.tc_term);
        type_of = (uu___262_20451.type_of);
        universe_of = (uu___262_20451.universe_of);
        check_type_of = (uu___262_20451.check_type_of);
        use_bv_sorts = (uu___262_20451.use_bv_sorts);
        qtbl_name_and_index = (uu___262_20451.qtbl_name_and_index);
        normalized_eff_names = (uu___262_20451.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___262_20451.synth_hook);
        splice = (uu___262_20451.splice);
        is_native_tactic = (uu___262_20451.is_native_tactic);
        identifier_info = (uu___262_20451.identifier_info);
        tc_hooks = (uu___262_20451.tc_hooks);
        dsenv = (uu___262_20451.dsenv);
        dep_graph = (uu___262_20451.dep_graph);
        nbe = (uu___262_20451.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20466 = FStar_Syntax_Free.names t  in
      let uu____20469 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20466 uu____20469
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20490 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20490
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20498 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20498
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20515 =
      match uu____20515 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20525 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20525)
       in
    let uu____20527 =
      let uu____20530 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20530 FStar_List.rev  in
    FStar_All.pipe_right uu____20527 (FStar_String.concat " ")
  
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
                  (let uu____20583 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20583 with
                   | FStar_Pervasives_Native.Some uu____20586 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20587 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20593;
        univ_ineqs = uu____20594; implicits = uu____20595;_} -> true
    | uu____20606 -> false
  
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
          let uu___263_20633 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___263_20633.deferred);
            univ_ineqs = (uu___263_20633.univ_ineqs);
            implicits = (uu___263_20633.implicits)
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
          let uu____20668 = FStar_Options.defensive ()  in
          if uu____20668
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20672 =
              let uu____20673 =
                let uu____20674 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20674  in
              Prims.op_Negation uu____20673  in
            (if uu____20672
             then
               let uu____20679 =
                 let uu____20684 =
                   let uu____20685 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20686 =
                     let uu____20687 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20687
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20685 uu____20686
                    in
                 (FStar_Errors.Warning_Defensive, uu____20684)  in
               FStar_Errors.log_issue rng uu____20679
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
          let uu____20718 =
            let uu____20719 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20719  in
          if uu____20718
          then ()
          else
            (let uu____20721 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20721 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20744 =
            let uu____20745 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20745  in
          if uu____20744
          then ()
          else
            (let uu____20747 = bound_vars e  in
             def_check_closed_in rng msg uu____20747 t)
  
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
          let uu___264_20782 = g  in
          let uu____20783 =
            let uu____20784 =
              let uu____20785 =
                let uu____20792 =
                  let uu____20793 =
                    let uu____20810 =
                      let uu____20821 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20821]  in
                    (f, uu____20810)  in
                  FStar_Syntax_Syntax.Tm_app uu____20793  in
                FStar_Syntax_Syntax.mk uu____20792  in
              uu____20785 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20784
             in
          {
            guard_f = uu____20783;
            deferred = (uu___264_20782.deferred);
            univ_ineqs = (uu___264_20782.univ_ineqs);
            implicits = (uu___264_20782.implicits)
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
          let uu___265_20877 = g  in
          let uu____20878 =
            let uu____20879 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20879  in
          {
            guard_f = uu____20878;
            deferred = (uu___265_20877.deferred);
            univ_ineqs = (uu___265_20877.univ_ineqs);
            implicits = (uu___265_20877.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___266_20895 = g  in
          let uu____20896 =
            let uu____20897 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____20897  in
          {
            guard_f = uu____20896;
            deferred = (uu___266_20895.deferred);
            univ_ineqs = (uu___266_20895.univ_ineqs);
            implicits = (uu___266_20895.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___267_20899 = g  in
          let uu____20900 =
            let uu____20901 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20901  in
          {
            guard_f = uu____20900;
            deferred = (uu___267_20899.deferred);
            univ_ineqs = (uu___267_20899.univ_ineqs);
            implicits = (uu___267_20899.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20907 ->
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
          let uu____20922 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____20922
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____20928 =
      let uu____20929 = FStar_Syntax_Util.unmeta t  in
      uu____20929.FStar_Syntax_Syntax.n  in
    match uu____20928 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____20933 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____20974 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____20974;
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
                       let uu____21055 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21055
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___268_21059 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___268_21059.deferred);
              univ_ineqs = (uu___268_21059.univ_ineqs);
              implicits = (uu___268_21059.implicits)
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
               let uu____21092 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21092
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
            let uu___269_21115 = g  in
            let uu____21116 =
              let uu____21117 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21117  in
            {
              guard_f = uu____21116;
              deferred = (uu___269_21115.deferred);
              univ_ineqs = (uu___269_21115.univ_ineqs);
              implicits = (uu___269_21115.implicits)
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
            let uu____21155 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21155 with
            | FStar_Pervasives_Native.Some
                (uu____21180::(tm,uu____21182)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21246 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21264 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21264;
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
                    let uu___270_21299 = trivial_guard  in
                    {
                      guard_f = (uu___270_21299.guard_f);
                      deferred = (uu___270_21299.deferred);
                      univ_ineqs = (uu___270_21299.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21316  -> ());
    push = (fun uu____21318  -> ());
    pop = (fun uu____21320  -> ());
    snapshot =
      (fun uu____21322  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21331  -> fun uu____21332  -> ());
    encode_modul = (fun uu____21343  -> fun uu____21344  -> ());
    encode_sig = (fun uu____21347  -> fun uu____21348  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21354 =
             let uu____21361 = FStar_Options.peek ()  in (e, g, uu____21361)
              in
           [uu____21354]);
    solve = (fun uu____21377  -> fun uu____21378  -> fun uu____21379  -> ());
    finish = (fun uu____21385  -> ());
    refresh = (fun uu____21387  -> ())
  } 