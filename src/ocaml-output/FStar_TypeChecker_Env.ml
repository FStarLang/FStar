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
      | (UnfoldAttr a1,UnfoldAttr a2) ->
          let uu____272 = FStar_Syntax_Util.eq_tm a1 a2  in
          uu____272 = FStar_Syntax_Util.Equal
      | uu____273 -> false
  
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
    match projectee with | NoDelta  -> true | uu____294 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____300 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____306 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____313 -> false
  
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
           (fun uu___223_9852  ->
              match uu___223_9852 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9855 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9855  in
                  let uu____9856 =
                    let uu____9857 = FStar_Syntax_Subst.compress y  in
                    uu____9857.FStar_Syntax_Syntax.n  in
                  (match uu____9856 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9861 =
                         let uu___237_9862 = y1  in
                         let uu____9863 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___237_9862.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___237_9862.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9863
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9861
                   | uu____9866 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___238_9878 = env  in
      let uu____9879 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___238_9878.solver);
        range = (uu___238_9878.range);
        curmodule = (uu___238_9878.curmodule);
        gamma = uu____9879;
        gamma_sig = (uu___238_9878.gamma_sig);
        gamma_cache = (uu___238_9878.gamma_cache);
        modules = (uu___238_9878.modules);
        expected_typ = (uu___238_9878.expected_typ);
        sigtab = (uu___238_9878.sigtab);
        attrtab = (uu___238_9878.attrtab);
        is_pattern = (uu___238_9878.is_pattern);
        instantiate_imp = (uu___238_9878.instantiate_imp);
        effects = (uu___238_9878.effects);
        generalize = (uu___238_9878.generalize);
        letrecs = (uu___238_9878.letrecs);
        top_level = (uu___238_9878.top_level);
        check_uvars = (uu___238_9878.check_uvars);
        use_eq = (uu___238_9878.use_eq);
        is_iface = (uu___238_9878.is_iface);
        admit = (uu___238_9878.admit);
        lax = (uu___238_9878.lax);
        lax_universes = (uu___238_9878.lax_universes);
        phase1 = (uu___238_9878.phase1);
        failhard = (uu___238_9878.failhard);
        nosynth = (uu___238_9878.nosynth);
        uvar_subtyping = (uu___238_9878.uvar_subtyping);
        tc_term = (uu___238_9878.tc_term);
        type_of = (uu___238_9878.type_of);
        universe_of = (uu___238_9878.universe_of);
        check_type_of = (uu___238_9878.check_type_of);
        use_bv_sorts = (uu___238_9878.use_bv_sorts);
        qtbl_name_and_index = (uu___238_9878.qtbl_name_and_index);
        normalized_eff_names = (uu___238_9878.normalized_eff_names);
        proof_ns = (uu___238_9878.proof_ns);
        synth_hook = (uu___238_9878.synth_hook);
        splice = (uu___238_9878.splice);
        is_native_tactic = (uu___238_9878.is_native_tactic);
        identifier_info = (uu___238_9878.identifier_info);
        tc_hooks = (uu___238_9878.tc_hooks);
        dsenv = (uu___238_9878.dsenv);
        dep_graph = (uu___238_9878.dep_graph);
        nbe = (uu___238_9878.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9886  -> fun uu____9887  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___239_9907 = env  in
      {
        solver = (uu___239_9907.solver);
        range = (uu___239_9907.range);
        curmodule = (uu___239_9907.curmodule);
        gamma = (uu___239_9907.gamma);
        gamma_sig = (uu___239_9907.gamma_sig);
        gamma_cache = (uu___239_9907.gamma_cache);
        modules = (uu___239_9907.modules);
        expected_typ = (uu___239_9907.expected_typ);
        sigtab = (uu___239_9907.sigtab);
        attrtab = (uu___239_9907.attrtab);
        is_pattern = (uu___239_9907.is_pattern);
        instantiate_imp = (uu___239_9907.instantiate_imp);
        effects = (uu___239_9907.effects);
        generalize = (uu___239_9907.generalize);
        letrecs = (uu___239_9907.letrecs);
        top_level = (uu___239_9907.top_level);
        check_uvars = (uu___239_9907.check_uvars);
        use_eq = (uu___239_9907.use_eq);
        is_iface = (uu___239_9907.is_iface);
        admit = (uu___239_9907.admit);
        lax = (uu___239_9907.lax);
        lax_universes = (uu___239_9907.lax_universes);
        phase1 = (uu___239_9907.phase1);
        failhard = (uu___239_9907.failhard);
        nosynth = (uu___239_9907.nosynth);
        uvar_subtyping = (uu___239_9907.uvar_subtyping);
        tc_term = (uu___239_9907.tc_term);
        type_of = (uu___239_9907.type_of);
        universe_of = (uu___239_9907.universe_of);
        check_type_of = (uu___239_9907.check_type_of);
        use_bv_sorts = (uu___239_9907.use_bv_sorts);
        qtbl_name_and_index = (uu___239_9907.qtbl_name_and_index);
        normalized_eff_names = (uu___239_9907.normalized_eff_names);
        proof_ns = (uu___239_9907.proof_ns);
        synth_hook = (uu___239_9907.synth_hook);
        splice = (uu___239_9907.splice);
        is_native_tactic = (uu___239_9907.is_native_tactic);
        identifier_info = (uu___239_9907.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___239_9907.dsenv);
        dep_graph = (uu___239_9907.dep_graph);
        nbe = (uu___239_9907.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___240_9918 = e  in
      {
        solver = (uu___240_9918.solver);
        range = (uu___240_9918.range);
        curmodule = (uu___240_9918.curmodule);
        gamma = (uu___240_9918.gamma);
        gamma_sig = (uu___240_9918.gamma_sig);
        gamma_cache = (uu___240_9918.gamma_cache);
        modules = (uu___240_9918.modules);
        expected_typ = (uu___240_9918.expected_typ);
        sigtab = (uu___240_9918.sigtab);
        attrtab = (uu___240_9918.attrtab);
        is_pattern = (uu___240_9918.is_pattern);
        instantiate_imp = (uu___240_9918.instantiate_imp);
        effects = (uu___240_9918.effects);
        generalize = (uu___240_9918.generalize);
        letrecs = (uu___240_9918.letrecs);
        top_level = (uu___240_9918.top_level);
        check_uvars = (uu___240_9918.check_uvars);
        use_eq = (uu___240_9918.use_eq);
        is_iface = (uu___240_9918.is_iface);
        admit = (uu___240_9918.admit);
        lax = (uu___240_9918.lax);
        lax_universes = (uu___240_9918.lax_universes);
        phase1 = (uu___240_9918.phase1);
        failhard = (uu___240_9918.failhard);
        nosynth = (uu___240_9918.nosynth);
        uvar_subtyping = (uu___240_9918.uvar_subtyping);
        tc_term = (uu___240_9918.tc_term);
        type_of = (uu___240_9918.type_of);
        universe_of = (uu___240_9918.universe_of);
        check_type_of = (uu___240_9918.check_type_of);
        use_bv_sorts = (uu___240_9918.use_bv_sorts);
        qtbl_name_and_index = (uu___240_9918.qtbl_name_and_index);
        normalized_eff_names = (uu___240_9918.normalized_eff_names);
        proof_ns = (uu___240_9918.proof_ns);
        synth_hook = (uu___240_9918.synth_hook);
        splice = (uu___240_9918.splice);
        is_native_tactic = (uu___240_9918.is_native_tactic);
        identifier_info = (uu___240_9918.identifier_info);
        tc_hooks = (uu___240_9918.tc_hooks);
        dsenv = (uu___240_9918.dsenv);
        dep_graph = g;
        nbe = (uu___240_9918.nbe)
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
      | (NoDelta ,uu____9941) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____9942,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____9943,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____9944 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____9953 . unit -> 'Auu____9953 FStar_Util.smap =
  fun uu____9960  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____9965 . unit -> 'Auu____9965 FStar_Util.smap =
  fun uu____9972  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____10106 = new_gamma_cache ()  in
                  let uu____10109 = new_sigtab ()  in
                  let uu____10112 = new_sigtab ()  in
                  let uu____10119 =
                    let uu____10132 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____10132, FStar_Pervasives_Native.None)  in
                  let uu____10147 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____10150 = FStar_Options.using_facts_from ()  in
                  let uu____10151 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____10154 = FStar_Syntax_DsEnv.empty_env ()  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10106;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10109;
                    attrtab = uu____10112;
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
                    qtbl_name_and_index = uu____10119;
                    normalized_eff_names = uu____10147;
                    proof_ns = uu____10150;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10190  -> false);
                    identifier_info = uu____10151;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10154;
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
  fun uu____10290  ->
    let uu____10291 = FStar_ST.op_Bang query_indices  in
    match uu____10291 with
    | [] -> failwith "Empty query indices!"
    | uu____10341 ->
        let uu____10350 =
          let uu____10359 =
            let uu____10366 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10366  in
          let uu____10416 = FStar_ST.op_Bang query_indices  in uu____10359 ::
            uu____10416
           in
        FStar_ST.op_Colon_Equals query_indices uu____10350
  
let (pop_query_indices : unit -> unit) =
  fun uu____10505  ->
    let uu____10506 = FStar_ST.op_Bang query_indices  in
    match uu____10506 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10621  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10651  ->
    match uu____10651 with
    | (l,n1) ->
        let uu____10658 = FStar_ST.op_Bang query_indices  in
        (match uu____10658 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10769 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10788  ->
    let uu____10789 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10789
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10862 =
       let uu____10865 = FStar_ST.op_Bang stack  in env :: uu____10865  in
     FStar_ST.op_Colon_Equals stack uu____10862);
    (let uu___241_10914 = env  in
     let uu____10915 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____10918 = FStar_Util.smap_copy (sigtab env)  in
     let uu____10921 = FStar_Util.smap_copy (attrtab env)  in
     let uu____10928 =
       let uu____10941 =
         let uu____10944 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____10944  in
       let uu____10969 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____10941, uu____10969)  in
     let uu____11010 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____11013 =
       let uu____11016 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____11016  in
     {
       solver = (uu___241_10914.solver);
       range = (uu___241_10914.range);
       curmodule = (uu___241_10914.curmodule);
       gamma = (uu___241_10914.gamma);
       gamma_sig = (uu___241_10914.gamma_sig);
       gamma_cache = uu____10915;
       modules = (uu___241_10914.modules);
       expected_typ = (uu___241_10914.expected_typ);
       sigtab = uu____10918;
       attrtab = uu____10921;
       is_pattern = (uu___241_10914.is_pattern);
       instantiate_imp = (uu___241_10914.instantiate_imp);
       effects = (uu___241_10914.effects);
       generalize = (uu___241_10914.generalize);
       letrecs = (uu___241_10914.letrecs);
       top_level = (uu___241_10914.top_level);
       check_uvars = (uu___241_10914.check_uvars);
       use_eq = (uu___241_10914.use_eq);
       is_iface = (uu___241_10914.is_iface);
       admit = (uu___241_10914.admit);
       lax = (uu___241_10914.lax);
       lax_universes = (uu___241_10914.lax_universes);
       phase1 = (uu___241_10914.phase1);
       failhard = (uu___241_10914.failhard);
       nosynth = (uu___241_10914.nosynth);
       uvar_subtyping = (uu___241_10914.uvar_subtyping);
       tc_term = (uu___241_10914.tc_term);
       type_of = (uu___241_10914.type_of);
       universe_of = (uu___241_10914.universe_of);
       check_type_of = (uu___241_10914.check_type_of);
       use_bv_sorts = (uu___241_10914.use_bv_sorts);
       qtbl_name_and_index = uu____10928;
       normalized_eff_names = uu____11010;
       proof_ns = (uu___241_10914.proof_ns);
       synth_hook = (uu___241_10914.synth_hook);
       splice = (uu___241_10914.splice);
       is_native_tactic = (uu___241_10914.is_native_tactic);
       identifier_info = uu____11013;
       tc_hooks = (uu___241_10914.tc_hooks);
       dsenv = (uu___241_10914.dsenv);
       dep_graph = (uu___241_10914.dep_graph);
       nbe = (uu___241_10914.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11062  ->
    let uu____11063 = FStar_ST.op_Bang stack  in
    match uu____11063 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11117 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____11189  ->
           let uu____11190 = snapshot_stack env  in
           match uu____11190 with
           | (stack_depth,env1) ->
               let uu____11215 = snapshot_query_indices ()  in
               (match uu____11215 with
                | (query_indices_depth,()) ->
                    let uu____11239 = (env1.solver).snapshot msg  in
                    (match uu____11239 with
                     | (solver_depth,()) ->
                         let uu____11281 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11281 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___242_11327 = env1  in
                                 {
                                   solver = (uu___242_11327.solver);
                                   range = (uu___242_11327.range);
                                   curmodule = (uu___242_11327.curmodule);
                                   gamma = (uu___242_11327.gamma);
                                   gamma_sig = (uu___242_11327.gamma_sig);
                                   gamma_cache = (uu___242_11327.gamma_cache);
                                   modules = (uu___242_11327.modules);
                                   expected_typ =
                                     (uu___242_11327.expected_typ);
                                   sigtab = (uu___242_11327.sigtab);
                                   attrtab = (uu___242_11327.attrtab);
                                   is_pattern = (uu___242_11327.is_pattern);
                                   instantiate_imp =
                                     (uu___242_11327.instantiate_imp);
                                   effects = (uu___242_11327.effects);
                                   generalize = (uu___242_11327.generalize);
                                   letrecs = (uu___242_11327.letrecs);
                                   top_level = (uu___242_11327.top_level);
                                   check_uvars = (uu___242_11327.check_uvars);
                                   use_eq = (uu___242_11327.use_eq);
                                   is_iface = (uu___242_11327.is_iface);
                                   admit = (uu___242_11327.admit);
                                   lax = (uu___242_11327.lax);
                                   lax_universes =
                                     (uu___242_11327.lax_universes);
                                   phase1 = (uu___242_11327.phase1);
                                   failhard = (uu___242_11327.failhard);
                                   nosynth = (uu___242_11327.nosynth);
                                   uvar_subtyping =
                                     (uu___242_11327.uvar_subtyping);
                                   tc_term = (uu___242_11327.tc_term);
                                   type_of = (uu___242_11327.type_of);
                                   universe_of = (uu___242_11327.universe_of);
                                   check_type_of =
                                     (uu___242_11327.check_type_of);
                                   use_bv_sorts =
                                     (uu___242_11327.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___242_11327.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___242_11327.normalized_eff_names);
                                   proof_ns = (uu___242_11327.proof_ns);
                                   synth_hook = (uu___242_11327.synth_hook);
                                   splice = (uu___242_11327.splice);
                                   is_native_tactic =
                                     (uu___242_11327.is_native_tactic);
                                   identifier_info =
                                     (uu___242_11327.identifier_info);
                                   tc_hooks = (uu___242_11327.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___242_11327.dep_graph);
                                   nbe = (uu___242_11327.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11358  ->
             let uu____11359 =
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
             match uu____11359 with
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
                             ((let uu____11485 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11485
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11496 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11496
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11523,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11555 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11581  ->
                  match uu____11581 with
                  | (m,uu____11587) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11555 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___243_11595 = env  in
               {
                 solver = (uu___243_11595.solver);
                 range = (uu___243_11595.range);
                 curmodule = (uu___243_11595.curmodule);
                 gamma = (uu___243_11595.gamma);
                 gamma_sig = (uu___243_11595.gamma_sig);
                 gamma_cache = (uu___243_11595.gamma_cache);
                 modules = (uu___243_11595.modules);
                 expected_typ = (uu___243_11595.expected_typ);
                 sigtab = (uu___243_11595.sigtab);
                 attrtab = (uu___243_11595.attrtab);
                 is_pattern = (uu___243_11595.is_pattern);
                 instantiate_imp = (uu___243_11595.instantiate_imp);
                 effects = (uu___243_11595.effects);
                 generalize = (uu___243_11595.generalize);
                 letrecs = (uu___243_11595.letrecs);
                 top_level = (uu___243_11595.top_level);
                 check_uvars = (uu___243_11595.check_uvars);
                 use_eq = (uu___243_11595.use_eq);
                 is_iface = (uu___243_11595.is_iface);
                 admit = (uu___243_11595.admit);
                 lax = (uu___243_11595.lax);
                 lax_universes = (uu___243_11595.lax_universes);
                 phase1 = (uu___243_11595.phase1);
                 failhard = (uu___243_11595.failhard);
                 nosynth = (uu___243_11595.nosynth);
                 uvar_subtyping = (uu___243_11595.uvar_subtyping);
                 tc_term = (uu___243_11595.tc_term);
                 type_of = (uu___243_11595.type_of);
                 universe_of = (uu___243_11595.universe_of);
                 check_type_of = (uu___243_11595.check_type_of);
                 use_bv_sorts = (uu___243_11595.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___243_11595.normalized_eff_names);
                 proof_ns = (uu___243_11595.proof_ns);
                 synth_hook = (uu___243_11595.synth_hook);
                 splice = (uu___243_11595.splice);
                 is_native_tactic = (uu___243_11595.is_native_tactic);
                 identifier_info = (uu___243_11595.identifier_info);
                 tc_hooks = (uu___243_11595.tc_hooks);
                 dsenv = (uu___243_11595.dsenv);
                 dep_graph = (uu___243_11595.dep_graph);
                 nbe = (uu___243_11595.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11608,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___244_11617 = env  in
               {
                 solver = (uu___244_11617.solver);
                 range = (uu___244_11617.range);
                 curmodule = (uu___244_11617.curmodule);
                 gamma = (uu___244_11617.gamma);
                 gamma_sig = (uu___244_11617.gamma_sig);
                 gamma_cache = (uu___244_11617.gamma_cache);
                 modules = (uu___244_11617.modules);
                 expected_typ = (uu___244_11617.expected_typ);
                 sigtab = (uu___244_11617.sigtab);
                 attrtab = (uu___244_11617.attrtab);
                 is_pattern = (uu___244_11617.is_pattern);
                 instantiate_imp = (uu___244_11617.instantiate_imp);
                 effects = (uu___244_11617.effects);
                 generalize = (uu___244_11617.generalize);
                 letrecs = (uu___244_11617.letrecs);
                 top_level = (uu___244_11617.top_level);
                 check_uvars = (uu___244_11617.check_uvars);
                 use_eq = (uu___244_11617.use_eq);
                 is_iface = (uu___244_11617.is_iface);
                 admit = (uu___244_11617.admit);
                 lax = (uu___244_11617.lax);
                 lax_universes = (uu___244_11617.lax_universes);
                 phase1 = (uu___244_11617.phase1);
                 failhard = (uu___244_11617.failhard);
                 nosynth = (uu___244_11617.nosynth);
                 uvar_subtyping = (uu___244_11617.uvar_subtyping);
                 tc_term = (uu___244_11617.tc_term);
                 type_of = (uu___244_11617.type_of);
                 universe_of = (uu___244_11617.universe_of);
                 check_type_of = (uu___244_11617.check_type_of);
                 use_bv_sorts = (uu___244_11617.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___244_11617.normalized_eff_names);
                 proof_ns = (uu___244_11617.proof_ns);
                 synth_hook = (uu___244_11617.synth_hook);
                 splice = (uu___244_11617.splice);
                 is_native_tactic = (uu___244_11617.is_native_tactic);
                 identifier_info = (uu___244_11617.identifier_info);
                 tc_hooks = (uu___244_11617.tc_hooks);
                 dsenv = (uu___244_11617.dsenv);
                 dep_graph = (uu___244_11617.dep_graph);
                 nbe = (uu___244_11617.nbe)
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
        (let uu___245_11651 = e  in
         {
           solver = (uu___245_11651.solver);
           range = r;
           curmodule = (uu___245_11651.curmodule);
           gamma = (uu___245_11651.gamma);
           gamma_sig = (uu___245_11651.gamma_sig);
           gamma_cache = (uu___245_11651.gamma_cache);
           modules = (uu___245_11651.modules);
           expected_typ = (uu___245_11651.expected_typ);
           sigtab = (uu___245_11651.sigtab);
           attrtab = (uu___245_11651.attrtab);
           is_pattern = (uu___245_11651.is_pattern);
           instantiate_imp = (uu___245_11651.instantiate_imp);
           effects = (uu___245_11651.effects);
           generalize = (uu___245_11651.generalize);
           letrecs = (uu___245_11651.letrecs);
           top_level = (uu___245_11651.top_level);
           check_uvars = (uu___245_11651.check_uvars);
           use_eq = (uu___245_11651.use_eq);
           is_iface = (uu___245_11651.is_iface);
           admit = (uu___245_11651.admit);
           lax = (uu___245_11651.lax);
           lax_universes = (uu___245_11651.lax_universes);
           phase1 = (uu___245_11651.phase1);
           failhard = (uu___245_11651.failhard);
           nosynth = (uu___245_11651.nosynth);
           uvar_subtyping = (uu___245_11651.uvar_subtyping);
           tc_term = (uu___245_11651.tc_term);
           type_of = (uu___245_11651.type_of);
           universe_of = (uu___245_11651.universe_of);
           check_type_of = (uu___245_11651.check_type_of);
           use_bv_sorts = (uu___245_11651.use_bv_sorts);
           qtbl_name_and_index = (uu___245_11651.qtbl_name_and_index);
           normalized_eff_names = (uu___245_11651.normalized_eff_names);
           proof_ns = (uu___245_11651.proof_ns);
           synth_hook = (uu___245_11651.synth_hook);
           splice = (uu___245_11651.splice);
           is_native_tactic = (uu___245_11651.is_native_tactic);
           identifier_info = (uu___245_11651.identifier_info);
           tc_hooks = (uu___245_11651.tc_hooks);
           dsenv = (uu___245_11651.dsenv);
           dep_graph = (uu___245_11651.dep_graph);
           nbe = (uu___245_11651.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11667 =
        let uu____11668 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11668 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11667
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11722 =
          let uu____11723 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11723 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11722
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11777 =
          let uu____11778 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11778 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11777
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11832 =
        let uu____11833 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11833 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11832
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___246_11894 = env  in
      {
        solver = (uu___246_11894.solver);
        range = (uu___246_11894.range);
        curmodule = lid;
        gamma = (uu___246_11894.gamma);
        gamma_sig = (uu___246_11894.gamma_sig);
        gamma_cache = (uu___246_11894.gamma_cache);
        modules = (uu___246_11894.modules);
        expected_typ = (uu___246_11894.expected_typ);
        sigtab = (uu___246_11894.sigtab);
        attrtab = (uu___246_11894.attrtab);
        is_pattern = (uu___246_11894.is_pattern);
        instantiate_imp = (uu___246_11894.instantiate_imp);
        effects = (uu___246_11894.effects);
        generalize = (uu___246_11894.generalize);
        letrecs = (uu___246_11894.letrecs);
        top_level = (uu___246_11894.top_level);
        check_uvars = (uu___246_11894.check_uvars);
        use_eq = (uu___246_11894.use_eq);
        is_iface = (uu___246_11894.is_iface);
        admit = (uu___246_11894.admit);
        lax = (uu___246_11894.lax);
        lax_universes = (uu___246_11894.lax_universes);
        phase1 = (uu___246_11894.phase1);
        failhard = (uu___246_11894.failhard);
        nosynth = (uu___246_11894.nosynth);
        uvar_subtyping = (uu___246_11894.uvar_subtyping);
        tc_term = (uu___246_11894.tc_term);
        type_of = (uu___246_11894.type_of);
        universe_of = (uu___246_11894.universe_of);
        check_type_of = (uu___246_11894.check_type_of);
        use_bv_sorts = (uu___246_11894.use_bv_sorts);
        qtbl_name_and_index = (uu___246_11894.qtbl_name_and_index);
        normalized_eff_names = (uu___246_11894.normalized_eff_names);
        proof_ns = (uu___246_11894.proof_ns);
        synth_hook = (uu___246_11894.synth_hook);
        splice = (uu___246_11894.splice);
        is_native_tactic = (uu___246_11894.is_native_tactic);
        identifier_info = (uu___246_11894.identifier_info);
        tc_hooks = (uu___246_11894.tc_hooks);
        dsenv = (uu___246_11894.dsenv);
        dep_graph = (uu___246_11894.dep_graph);
        nbe = (uu___246_11894.nbe)
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
      let uu____11921 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11921
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11931 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11931)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11941 =
      let uu____11942 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11942  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11941)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11947  ->
    let uu____11948 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11948
  
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
      | ((formals,t),uu____12032) ->
          let vs = mk_univ_subst formals us  in
          let uu____12056 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12056)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___224_12072  ->
    match uu___224_12072 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12098  -> new_u_univ ()))
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
      let uu____12117 = inst_tscheme t  in
      match uu____12117 with
      | (us,t1) ->
          let uu____12128 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12128)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12148  ->
          match uu____12148 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12169 =
                         let uu____12170 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12171 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12172 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12173 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12170 uu____12171 uu____12172 uu____12173
                          in
                       failwith uu____12169)
                    else ();
                    (let uu____12175 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12175))
               | uu____12184 ->
                   let uu____12185 =
                     let uu____12186 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12186
                      in
                   failwith uu____12185)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12192 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12198 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12204 -> false
  
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
             | ([],uu____12246) -> Maybe
             | (uu____12253,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12272 -> No  in
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
          let uu____12363 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12363 with
          | FStar_Pervasives_Native.None  ->
              let uu____12386 =
                FStar_Util.find_map env.gamma
                  (fun uu___225_12430  ->
                     match uu___225_12430 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12469 = FStar_Ident.lid_equals lid l  in
                         if uu____12469
                         then
                           let uu____12490 =
                             let uu____12509 =
                               let uu____12524 = inst_tscheme t  in
                               FStar_Util.Inl uu____12524  in
                             let uu____12539 = FStar_Ident.range_of_lid l  in
                             (uu____12509, uu____12539)  in
                           FStar_Pervasives_Native.Some uu____12490
                         else FStar_Pervasives_Native.None
                     | uu____12591 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12386
                (fun uu____12629  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___226_12638  ->
                        match uu___226_12638 with
                        | (uu____12641,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12643);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12644;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12645;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12646;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12647;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12667 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12667
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
                                  uu____12715 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12722 -> cache t  in
                            let uu____12723 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12723 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12729 =
                                   let uu____12730 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12730)
                                    in
                                 maybe_cache uu____12729)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12798 = find_in_sigtab env lid  in
         match uu____12798 with
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
      let uu____12878 = lookup_qname env lid  in
      match uu____12878 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12899,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13010 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13010 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13052 =
          let uu____13055 = lookup_attr env1 attr  in se1 :: uu____13055  in
        FStar_Util.smap_add (attrtab env1) attr uu____13052  in
      FStar_List.iter
        (fun attr  ->
           let uu____13065 =
             let uu____13066 = FStar_Syntax_Subst.compress attr  in
             uu____13066.FStar_Syntax_Syntax.n  in
           match uu____13065 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13070 =
                 let uu____13071 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13071.FStar_Ident.str  in
               add_one1 env se uu____13070
           | uu____13072 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13094) ->
          add_sigelts env ses
      | uu____13103 ->
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
            | uu____13118 -> ()))

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
        (fun uu___227_13149  ->
           match uu___227_13149 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13167 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13228,lb::[]),uu____13230) ->
            let uu____13237 =
              let uu____13246 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13255 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13246, uu____13255)  in
            FStar_Pervasives_Native.Some uu____13237
        | FStar_Syntax_Syntax.Sig_let ((uu____13268,lbs),uu____13270) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13300 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13312 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13312
                     then
                       let uu____13323 =
                         let uu____13332 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13341 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13332, uu____13341)  in
                       FStar_Pervasives_Native.Some uu____13323
                     else FStar_Pervasives_Native.None)
        | uu____13363 -> FStar_Pervasives_Native.None
  
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
          let uu____13422 =
            let uu____13431 =
              let uu____13436 =
                let uu____13437 =
                  let uu____13440 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13440
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13437)  in
              inst_tscheme1 uu____13436  in
            (uu____13431, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13422
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13462,uu____13463) ->
          let uu____13468 =
            let uu____13477 =
              let uu____13482 =
                let uu____13483 =
                  let uu____13486 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13486  in
                (us, uu____13483)  in
              inst_tscheme1 uu____13482  in
            (uu____13477, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13468
      | uu____13505 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13593 =
          match uu____13593 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13689,uvs,t,uu____13692,uu____13693,uu____13694);
                      FStar_Syntax_Syntax.sigrng = uu____13695;
                      FStar_Syntax_Syntax.sigquals = uu____13696;
                      FStar_Syntax_Syntax.sigmeta = uu____13697;
                      FStar_Syntax_Syntax.sigattrs = uu____13698;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13719 =
                     let uu____13728 = inst_tscheme1 (uvs, t)  in
                     (uu____13728, rng)  in
                   FStar_Pervasives_Native.Some uu____13719
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13752;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13754;
                      FStar_Syntax_Syntax.sigattrs = uu____13755;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13772 =
                     let uu____13773 = in_cur_mod env l  in uu____13773 = Yes
                      in
                   if uu____13772
                   then
                     let uu____13784 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13784
                      then
                        let uu____13797 =
                          let uu____13806 = inst_tscheme1 (uvs, t)  in
                          (uu____13806, rng)  in
                        FStar_Pervasives_Native.Some uu____13797
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13837 =
                        let uu____13846 = inst_tscheme1 (uvs, t)  in
                        (uu____13846, rng)  in
                      FStar_Pervasives_Native.Some uu____13837)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13871,uu____13872);
                      FStar_Syntax_Syntax.sigrng = uu____13873;
                      FStar_Syntax_Syntax.sigquals = uu____13874;
                      FStar_Syntax_Syntax.sigmeta = uu____13875;
                      FStar_Syntax_Syntax.sigattrs = uu____13876;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13917 =
                          let uu____13926 = inst_tscheme1 (uvs, k)  in
                          (uu____13926, rng)  in
                        FStar_Pervasives_Native.Some uu____13917
                    | uu____13947 ->
                        let uu____13948 =
                          let uu____13957 =
                            let uu____13962 =
                              let uu____13963 =
                                let uu____13966 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13966
                                 in
                              (uvs, uu____13963)  in
                            inst_tscheme1 uu____13962  in
                          (uu____13957, rng)  in
                        FStar_Pervasives_Native.Some uu____13948)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13989,uu____13990);
                      FStar_Syntax_Syntax.sigrng = uu____13991;
                      FStar_Syntax_Syntax.sigquals = uu____13992;
                      FStar_Syntax_Syntax.sigmeta = uu____13993;
                      FStar_Syntax_Syntax.sigattrs = uu____13994;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14036 =
                          let uu____14045 = inst_tscheme_with (uvs, k) us  in
                          (uu____14045, rng)  in
                        FStar_Pervasives_Native.Some uu____14036
                    | uu____14066 ->
                        let uu____14067 =
                          let uu____14076 =
                            let uu____14081 =
                              let uu____14082 =
                                let uu____14085 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14085
                                 in
                              (uvs, uu____14082)  in
                            inst_tscheme_with uu____14081 us  in
                          (uu____14076, rng)  in
                        FStar_Pervasives_Native.Some uu____14067)
               | FStar_Util.Inr se ->
                   let uu____14121 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14142;
                          FStar_Syntax_Syntax.sigrng = uu____14143;
                          FStar_Syntax_Syntax.sigquals = uu____14144;
                          FStar_Syntax_Syntax.sigmeta = uu____14145;
                          FStar_Syntax_Syntax.sigattrs = uu____14146;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14161 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14121
                     (FStar_Util.map_option
                        (fun uu____14209  ->
                           match uu____14209 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14240 =
          let uu____14251 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14251 mapper  in
        match uu____14240 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14325 =
              let uu____14336 =
                let uu____14343 =
                  let uu___247_14346 = t  in
                  let uu____14347 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___247_14346.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14347;
                    FStar_Syntax_Syntax.vars =
                      (uu___247_14346.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14343)  in
              (uu____14336, r)  in
            FStar_Pervasives_Native.Some uu____14325
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14394 = lookup_qname env l  in
      match uu____14394 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14413 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14465 = try_lookup_bv env bv  in
      match uu____14465 with
      | FStar_Pervasives_Native.None  ->
          let uu____14480 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14480 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14495 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14496 =
            let uu____14497 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14497  in
          (uu____14495, uu____14496)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14518 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14518 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14584 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14584  in
          let uu____14585 =
            let uu____14594 =
              let uu____14599 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14599)  in
            (uu____14594, r1)  in
          FStar_Pervasives_Native.Some uu____14585
  
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
        let uu____14633 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14633 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14666,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14691 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14691  in
            let uu____14692 =
              let uu____14697 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14697, r1)  in
            FStar_Pervasives_Native.Some uu____14692
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14720 = try_lookup_lid env l  in
      match uu____14720 with
      | FStar_Pervasives_Native.None  ->
          let uu____14747 = name_not_found l  in
          let uu____14752 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14747 uu____14752
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___228_14792  ->
              match uu___228_14792 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14794 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14813 = lookup_qname env lid  in
      match uu____14813 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14822,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14825;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14827;
              FStar_Syntax_Syntax.sigattrs = uu____14828;_},FStar_Pervasives_Native.None
            ),uu____14829)
          ->
          let uu____14878 =
            let uu____14885 =
              let uu____14886 =
                let uu____14889 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14889 t  in
              (uvs, uu____14886)  in
            (uu____14885, q)  in
          FStar_Pervasives_Native.Some uu____14878
      | uu____14902 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14923 = lookup_qname env lid  in
      match uu____14923 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14928,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14931;
              FStar_Syntax_Syntax.sigquals = uu____14932;
              FStar_Syntax_Syntax.sigmeta = uu____14933;
              FStar_Syntax_Syntax.sigattrs = uu____14934;_},FStar_Pervasives_Native.None
            ),uu____14935)
          ->
          let uu____14984 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14984 (uvs, t)
      | uu____14989 ->
          let uu____14990 = name_not_found lid  in
          let uu____14995 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14990 uu____14995
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15014 = lookup_qname env lid  in
      match uu____15014 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15019,uvs,t,uu____15022,uu____15023,uu____15024);
              FStar_Syntax_Syntax.sigrng = uu____15025;
              FStar_Syntax_Syntax.sigquals = uu____15026;
              FStar_Syntax_Syntax.sigmeta = uu____15027;
              FStar_Syntax_Syntax.sigattrs = uu____15028;_},FStar_Pervasives_Native.None
            ),uu____15029)
          ->
          let uu____15082 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15082 (uvs, t)
      | uu____15087 ->
          let uu____15088 = name_not_found lid  in
          let uu____15093 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15088 uu____15093
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15114 = lookup_qname env lid  in
      match uu____15114 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15121,uu____15122,uu____15123,uu____15124,uu____15125,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15127;
              FStar_Syntax_Syntax.sigquals = uu____15128;
              FStar_Syntax_Syntax.sigmeta = uu____15129;
              FStar_Syntax_Syntax.sigattrs = uu____15130;_},uu____15131),uu____15132)
          -> (true, dcs)
      | uu____15193 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15206 = lookup_qname env lid  in
      match uu____15206 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15207,uu____15208,uu____15209,l,uu____15211,uu____15212);
              FStar_Syntax_Syntax.sigrng = uu____15213;
              FStar_Syntax_Syntax.sigquals = uu____15214;
              FStar_Syntax_Syntax.sigmeta = uu____15215;
              FStar_Syntax_Syntax.sigattrs = uu____15216;_},uu____15217),uu____15218)
          -> l
      | uu____15273 ->
          let uu____15274 =
            let uu____15275 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15275  in
          failwith uu____15274
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15324)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15375,lbs),uu____15377)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15399 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15399
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15431 -> FStar_Pervasives_Native.None)
        | uu____15436 -> FStar_Pervasives_Native.None
  
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
        let uu____15466 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15466
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15491),uu____15492) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15541 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15562),uu____15563) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15612 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15633 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15633
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15652 = lookup_qname env ftv  in
      match uu____15652 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15656) ->
          let uu____15701 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15701 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15722,t),r) ->
               let uu____15737 =
                 let uu____15738 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15738 t  in
               FStar_Pervasives_Native.Some uu____15737)
      | uu____15739 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15750 = try_lookup_effect_lid env ftv  in
      match uu____15750 with
      | FStar_Pervasives_Native.None  ->
          let uu____15753 = name_not_found ftv  in
          let uu____15758 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15753 uu____15758
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
        let uu____15781 = lookup_qname env lid0  in
        match uu____15781 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15792);
                FStar_Syntax_Syntax.sigrng = uu____15793;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15795;
                FStar_Syntax_Syntax.sigattrs = uu____15796;_},FStar_Pervasives_Native.None
              ),uu____15797)
            ->
            let lid1 =
              let uu____15851 =
                let uu____15852 = FStar_Ident.range_of_lid lid  in
                let uu____15853 =
                  let uu____15854 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____15854  in
                FStar_Range.set_use_range uu____15852 uu____15853  in
              FStar_Ident.set_lid_range lid uu____15851  in
            let uu____15855 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___229_15859  ->
                      match uu___229_15859 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____15860 -> false))
               in
            if uu____15855
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15874 =
                      let uu____15875 =
                        let uu____15876 = get_range env  in
                        FStar_Range.string_of_range uu____15876  in
                      let uu____15877 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____15878 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15875 uu____15877 uu____15878
                       in
                    failwith uu____15874)
                  in
               match (binders, univs1) with
               | ([],uu____15895) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____15920,uu____15921::uu____15922::uu____15923) ->
                   let uu____15944 =
                     let uu____15945 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____15946 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____15945 uu____15946
                      in
                   failwith uu____15944
               | uu____15953 ->
                   let uu____15968 =
                     let uu____15973 =
                       let uu____15974 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____15974)  in
                     inst_tscheme_with uu____15973 insts  in
                   (match uu____15968 with
                    | (uu____15987,t) ->
                        let t1 =
                          let uu____15990 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____15990 t  in
                        let uu____15991 =
                          let uu____15992 = FStar_Syntax_Subst.compress t1
                             in
                          uu____15992.FStar_Syntax_Syntax.n  in
                        (match uu____15991 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16027 -> failwith "Impossible")))
        | uu____16034 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16057 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16057 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16070,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16077 = find1 l2  in
            (match uu____16077 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16084 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16084 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16088 = find1 l  in
            (match uu____16088 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16093 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16093
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16107 = lookup_qname env l1  in
      match uu____16107 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16110;
              FStar_Syntax_Syntax.sigrng = uu____16111;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16113;
              FStar_Syntax_Syntax.sigattrs = uu____16114;_},uu____16115),uu____16116)
          -> q
      | uu____16167 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16188 =
          let uu____16189 =
            let uu____16190 = FStar_Util.string_of_int i  in
            let uu____16191 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16190 uu____16191
             in
          failwith uu____16189  in
        let uu____16192 = lookup_datacon env lid  in
        match uu____16192 with
        | (uu____16197,t) ->
            let uu____16199 =
              let uu____16200 = FStar_Syntax_Subst.compress t  in
              uu____16200.FStar_Syntax_Syntax.n  in
            (match uu____16199 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16204) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16245 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16245
                      FStar_Pervasives_Native.fst)
             | uu____16256 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16267 = lookup_qname env l  in
      match uu____16267 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16268,uu____16269,uu____16270);
              FStar_Syntax_Syntax.sigrng = uu____16271;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16273;
              FStar_Syntax_Syntax.sigattrs = uu____16274;_},uu____16275),uu____16276)
          ->
          FStar_Util.for_some
            (fun uu___230_16329  ->
               match uu___230_16329 with
               | FStar_Syntax_Syntax.Projector uu____16330 -> true
               | uu____16335 -> false) quals
      | uu____16336 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16347 = lookup_qname env lid  in
      match uu____16347 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16348,uu____16349,uu____16350,uu____16351,uu____16352,uu____16353);
              FStar_Syntax_Syntax.sigrng = uu____16354;
              FStar_Syntax_Syntax.sigquals = uu____16355;
              FStar_Syntax_Syntax.sigmeta = uu____16356;
              FStar_Syntax_Syntax.sigattrs = uu____16357;_},uu____16358),uu____16359)
          -> true
      | uu____16414 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16425 = lookup_qname env lid  in
      match uu____16425 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16426,uu____16427,uu____16428,uu____16429,uu____16430,uu____16431);
              FStar_Syntax_Syntax.sigrng = uu____16432;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16434;
              FStar_Syntax_Syntax.sigattrs = uu____16435;_},uu____16436),uu____16437)
          ->
          FStar_Util.for_some
            (fun uu___231_16498  ->
               match uu___231_16498 with
               | FStar_Syntax_Syntax.RecordType uu____16499 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16508 -> true
               | uu____16517 -> false) quals
      | uu____16518 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16524,uu____16525);
            FStar_Syntax_Syntax.sigrng = uu____16526;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16528;
            FStar_Syntax_Syntax.sigattrs = uu____16529;_},uu____16530),uu____16531)
        ->
        FStar_Util.for_some
          (fun uu___232_16588  ->
             match uu___232_16588 with
             | FStar_Syntax_Syntax.Action uu____16589 -> true
             | uu____16590 -> false) quals
    | uu____16591 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16602 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16602
  
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
      let uu____16616 =
        let uu____16617 = FStar_Syntax_Util.un_uinst head1  in
        uu____16617.FStar_Syntax_Syntax.n  in
      match uu____16616 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16621 ->
               true
           | uu____16622 -> false)
      | uu____16623 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16634 = lookup_qname env l  in
      match uu____16634 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16636),uu____16637) ->
          FStar_Util.for_some
            (fun uu___233_16685  ->
               match uu___233_16685 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16686 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16687 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16758 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16774) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16791 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16798 ->
                 FStar_Pervasives_Native.Some true
             | uu____16815 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16816 =
        let uu____16819 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16819 mapper  in
      match uu____16816 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____16869 = lookup_qname env lid  in
      match uu____16869 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16870,uu____16871,tps,uu____16873,uu____16874,uu____16875);
              FStar_Syntax_Syntax.sigrng = uu____16876;
              FStar_Syntax_Syntax.sigquals = uu____16877;
              FStar_Syntax_Syntax.sigmeta = uu____16878;
              FStar_Syntax_Syntax.sigattrs = uu____16879;_},uu____16880),uu____16881)
          -> FStar_List.length tps
      | uu____16946 ->
          let uu____16947 = name_not_found lid  in
          let uu____16952 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____16947 uu____16952
  
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
           (fun uu____16996  ->
              match uu____16996 with
              | (d,uu____17004) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17019 = effect_decl_opt env l  in
      match uu____17019 with
      | FStar_Pervasives_Native.None  ->
          let uu____17034 = name_not_found l  in
          let uu____17039 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17034 uu____17039
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17061  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17080  ->
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
        let uu____17111 = FStar_Ident.lid_equals l1 l2  in
        if uu____17111
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17119 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17119
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17127 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17180  ->
                        match uu____17180 with
                        | (m1,m2,uu____17193,uu____17194,uu____17195) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17127 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17212 =
                    let uu____17217 =
                      let uu____17218 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17219 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17218
                        uu____17219
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17217)
                     in
                  FStar_Errors.raise_error uu____17212 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17226,uu____17227,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17260 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17260
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
  'Auu____17276 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17276)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17305 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17331  ->
                match uu____17331 with
                | (d,uu____17337) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17305 with
      | FStar_Pervasives_Native.None  ->
          let uu____17348 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17348
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17361 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17361 with
           | (uu____17376,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17394)::(wp,uu____17396)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17452 -> failwith "Impossible"))
  
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
          let uu____17507 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17507
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17509 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17509
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
                  let uu____17517 = get_range env  in
                  let uu____17518 =
                    let uu____17525 =
                      let uu____17526 =
                        let uu____17543 =
                          let uu____17554 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17554]  in
                        (null_wp, uu____17543)  in
                      FStar_Syntax_Syntax.Tm_app uu____17526  in
                    FStar_Syntax_Syntax.mk uu____17525  in
                  uu____17518 FStar_Pervasives_Native.None uu____17517  in
                let uu____17594 =
                  let uu____17595 =
                    let uu____17606 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17606]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17595;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17594))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___248_17643 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___248_17643.order);
              joins = (uu___248_17643.joins)
            }  in
          let uu___249_17652 = env  in
          {
            solver = (uu___249_17652.solver);
            range = (uu___249_17652.range);
            curmodule = (uu___249_17652.curmodule);
            gamma = (uu___249_17652.gamma);
            gamma_sig = (uu___249_17652.gamma_sig);
            gamma_cache = (uu___249_17652.gamma_cache);
            modules = (uu___249_17652.modules);
            expected_typ = (uu___249_17652.expected_typ);
            sigtab = (uu___249_17652.sigtab);
            attrtab = (uu___249_17652.attrtab);
            is_pattern = (uu___249_17652.is_pattern);
            instantiate_imp = (uu___249_17652.instantiate_imp);
            effects;
            generalize = (uu___249_17652.generalize);
            letrecs = (uu___249_17652.letrecs);
            top_level = (uu___249_17652.top_level);
            check_uvars = (uu___249_17652.check_uvars);
            use_eq = (uu___249_17652.use_eq);
            is_iface = (uu___249_17652.is_iface);
            admit = (uu___249_17652.admit);
            lax = (uu___249_17652.lax);
            lax_universes = (uu___249_17652.lax_universes);
            phase1 = (uu___249_17652.phase1);
            failhard = (uu___249_17652.failhard);
            nosynth = (uu___249_17652.nosynth);
            uvar_subtyping = (uu___249_17652.uvar_subtyping);
            tc_term = (uu___249_17652.tc_term);
            type_of = (uu___249_17652.type_of);
            universe_of = (uu___249_17652.universe_of);
            check_type_of = (uu___249_17652.check_type_of);
            use_bv_sorts = (uu___249_17652.use_bv_sorts);
            qtbl_name_and_index = (uu___249_17652.qtbl_name_and_index);
            normalized_eff_names = (uu___249_17652.normalized_eff_names);
            proof_ns = (uu___249_17652.proof_ns);
            synth_hook = (uu___249_17652.synth_hook);
            splice = (uu___249_17652.splice);
            is_native_tactic = (uu___249_17652.is_native_tactic);
            identifier_info = (uu___249_17652.identifier_info);
            tc_hooks = (uu___249_17652.tc_hooks);
            dsenv = (uu___249_17652.dsenv);
            dep_graph = (uu___249_17652.dep_graph);
            nbe = (uu___249_17652.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17682 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17682  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____17840 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____17841 = l1 u t wp e  in
                                l2 u t uu____17840 uu____17841))
                | uu____17842 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____17914 = inst_tscheme_with lift_t [u]  in
            match uu____17914 with
            | (uu____17921,lift_t1) ->
                let uu____17923 =
                  let uu____17930 =
                    let uu____17931 =
                      let uu____17948 =
                        let uu____17959 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____17968 =
                          let uu____17979 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____17979]  in
                        uu____17959 :: uu____17968  in
                      (lift_t1, uu____17948)  in
                    FStar_Syntax_Syntax.Tm_app uu____17931  in
                  FStar_Syntax_Syntax.mk uu____17930  in
                uu____17923 FStar_Pervasives_Native.None
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
            let uu____18091 = inst_tscheme_with lift_t [u]  in
            match uu____18091 with
            | (uu____18098,lift_t1) ->
                let uu____18100 =
                  let uu____18107 =
                    let uu____18108 =
                      let uu____18125 =
                        let uu____18136 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18145 =
                          let uu____18156 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18165 =
                            let uu____18176 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18176]  in
                          uu____18156 :: uu____18165  in
                        uu____18136 :: uu____18145  in
                      (lift_t1, uu____18125)  in
                    FStar_Syntax_Syntax.Tm_app uu____18108  in
                  FStar_Syntax_Syntax.mk uu____18107  in
                uu____18100 FStar_Pervasives_Native.None
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
              let uu____18278 =
                let uu____18279 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18279
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18278  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18283 =
              let uu____18284 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18284  in
            let uu____18285 =
              let uu____18286 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18312 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18312)
                 in
              FStar_Util.dflt "none" uu____18286  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18283
              uu____18285
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18338  ->
                    match uu____18338 with
                    | (e,uu____18346) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18369 =
            match uu____18369 with
            | (i,j) ->
                let uu____18380 = FStar_Ident.lid_equals i j  in
                if uu____18380
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
              let uu____18412 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18422 = FStar_Ident.lid_equals i k  in
                        if uu____18422
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18433 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18433
                                  then []
                                  else
                                    (let uu____18437 =
                                       let uu____18446 =
                                         find_edge order1 (i, k)  in
                                       let uu____18449 =
                                         find_edge order1 (k, j)  in
                                       (uu____18446, uu____18449)  in
                                     match uu____18437 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18464 =
                                           compose_edges e1 e2  in
                                         [uu____18464]
                                     | uu____18465 -> [])))))
                 in
              FStar_List.append order1 uu____18412  in
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
                   let uu____18495 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18497 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18497
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18495
                   then
                     let uu____18502 =
                       let uu____18507 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18507)
                        in
                     let uu____18508 = get_range env  in
                     FStar_Errors.raise_error uu____18502 uu____18508
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18585 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18585
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18634 =
                                              let uu____18643 =
                                                find_edge order2 (i, k)  in
                                              let uu____18646 =
                                                find_edge order2 (j, k)  in
                                              (uu____18643, uu____18646)  in
                                            match uu____18634 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18688,uu____18689)
                                                     ->
                                                     let uu____18696 =
                                                       let uu____18701 =
                                                         let uu____18702 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18702
                                                          in
                                                       let uu____18705 =
                                                         let uu____18706 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18706
                                                          in
                                                       (uu____18701,
                                                         uu____18705)
                                                        in
                                                     (match uu____18696 with
                                                      | (true ,true ) ->
                                                          let uu____18717 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18717
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
                                            | uu____18742 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___250_18815 = env.effects  in
              { decls = (uu___250_18815.decls); order = order2; joins }  in
            let uu___251_18816 = env  in
            {
              solver = (uu___251_18816.solver);
              range = (uu___251_18816.range);
              curmodule = (uu___251_18816.curmodule);
              gamma = (uu___251_18816.gamma);
              gamma_sig = (uu___251_18816.gamma_sig);
              gamma_cache = (uu___251_18816.gamma_cache);
              modules = (uu___251_18816.modules);
              expected_typ = (uu___251_18816.expected_typ);
              sigtab = (uu___251_18816.sigtab);
              attrtab = (uu___251_18816.attrtab);
              is_pattern = (uu___251_18816.is_pattern);
              instantiate_imp = (uu___251_18816.instantiate_imp);
              effects;
              generalize = (uu___251_18816.generalize);
              letrecs = (uu___251_18816.letrecs);
              top_level = (uu___251_18816.top_level);
              check_uvars = (uu___251_18816.check_uvars);
              use_eq = (uu___251_18816.use_eq);
              is_iface = (uu___251_18816.is_iface);
              admit = (uu___251_18816.admit);
              lax = (uu___251_18816.lax);
              lax_universes = (uu___251_18816.lax_universes);
              phase1 = (uu___251_18816.phase1);
              failhard = (uu___251_18816.failhard);
              nosynth = (uu___251_18816.nosynth);
              uvar_subtyping = (uu___251_18816.uvar_subtyping);
              tc_term = (uu___251_18816.tc_term);
              type_of = (uu___251_18816.type_of);
              universe_of = (uu___251_18816.universe_of);
              check_type_of = (uu___251_18816.check_type_of);
              use_bv_sorts = (uu___251_18816.use_bv_sorts);
              qtbl_name_and_index = (uu___251_18816.qtbl_name_and_index);
              normalized_eff_names = (uu___251_18816.normalized_eff_names);
              proof_ns = (uu___251_18816.proof_ns);
              synth_hook = (uu___251_18816.synth_hook);
              splice = (uu___251_18816.splice);
              is_native_tactic = (uu___251_18816.is_native_tactic);
              identifier_info = (uu___251_18816.identifier_info);
              tc_hooks = (uu___251_18816.tc_hooks);
              dsenv = (uu___251_18816.dsenv);
              dep_graph = (uu___251_18816.dep_graph);
              nbe = (uu___251_18816.nbe)
            }))
      | uu____18817 -> env
  
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
        | uu____18845 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____18857 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____18857 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____18874 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____18874 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18896 =
                     let uu____18901 =
                       let uu____18902 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____18909 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____18918 =
                         let uu____18919 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____18919  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18902 uu____18909 uu____18918
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18901)
                      in
                   FStar_Errors.raise_error uu____18896
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____18924 =
                     let uu____18935 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____18935 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____18972  ->
                        fun uu____18973  ->
                          match (uu____18972, uu____18973) with
                          | ((x,uu____19003),(t,uu____19005)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____18924
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19036 =
                     let uu___252_19037 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___252_19037.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___252_19037.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___252_19037.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___252_19037.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19036
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
          let uu____19067 = effect_decl_opt env effect_name  in
          match uu____19067 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____19100 =
                only_reifiable &&
                  (let uu____19102 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____19102)
                 in
              if uu____19100
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____19118 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____19141 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____19178 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____19178
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____19179 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____19179
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____19193 =
                       let uu____19196 = get_range env  in
                       let uu____19197 =
                         let uu____19204 =
                           let uu____19205 =
                             let uu____19222 =
                               let uu____19233 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____19233; wp]  in
                             (repr, uu____19222)  in
                           FStar_Syntax_Syntax.Tm_app uu____19205  in
                         FStar_Syntax_Syntax.mk uu____19204  in
                       uu____19197 FStar_Pervasives_Native.None uu____19196
                        in
                     FStar_Pervasives_Native.Some uu____19193)
  
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
          let uu____19323 =
            let uu____19328 =
              let uu____19329 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____19329
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____19328)  in
          let uu____19330 = get_range env  in
          FStar_Errors.raise_error uu____19323 uu____19330  in
        let uu____19331 = effect_repr_aux true env c u_c  in
        match uu____19331 with
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
      | uu____19377 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19388 =
        let uu____19389 = FStar_Syntax_Subst.compress t  in
        uu____19389.FStar_Syntax_Syntax.n  in
      match uu____19388 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19392,c) ->
          is_reifiable_comp env c
      | uu____19414 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___253_19435 = env  in
        {
          solver = (uu___253_19435.solver);
          range = (uu___253_19435.range);
          curmodule = (uu___253_19435.curmodule);
          gamma = (uu___253_19435.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___253_19435.gamma_cache);
          modules = (uu___253_19435.modules);
          expected_typ = (uu___253_19435.expected_typ);
          sigtab = (uu___253_19435.sigtab);
          attrtab = (uu___253_19435.attrtab);
          is_pattern = (uu___253_19435.is_pattern);
          instantiate_imp = (uu___253_19435.instantiate_imp);
          effects = (uu___253_19435.effects);
          generalize = (uu___253_19435.generalize);
          letrecs = (uu___253_19435.letrecs);
          top_level = (uu___253_19435.top_level);
          check_uvars = (uu___253_19435.check_uvars);
          use_eq = (uu___253_19435.use_eq);
          is_iface = (uu___253_19435.is_iface);
          admit = (uu___253_19435.admit);
          lax = (uu___253_19435.lax);
          lax_universes = (uu___253_19435.lax_universes);
          phase1 = (uu___253_19435.phase1);
          failhard = (uu___253_19435.failhard);
          nosynth = (uu___253_19435.nosynth);
          uvar_subtyping = (uu___253_19435.uvar_subtyping);
          tc_term = (uu___253_19435.tc_term);
          type_of = (uu___253_19435.type_of);
          universe_of = (uu___253_19435.universe_of);
          check_type_of = (uu___253_19435.check_type_of);
          use_bv_sorts = (uu___253_19435.use_bv_sorts);
          qtbl_name_and_index = (uu___253_19435.qtbl_name_and_index);
          normalized_eff_names = (uu___253_19435.normalized_eff_names);
          proof_ns = (uu___253_19435.proof_ns);
          synth_hook = (uu___253_19435.synth_hook);
          splice = (uu___253_19435.splice);
          is_native_tactic = (uu___253_19435.is_native_tactic);
          identifier_info = (uu___253_19435.identifier_info);
          tc_hooks = (uu___253_19435.tc_hooks);
          dsenv = (uu___253_19435.dsenv);
          dep_graph = (uu___253_19435.dep_graph);
          nbe = (uu___253_19435.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___254_19448 = env  in
      {
        solver = (uu___254_19448.solver);
        range = (uu___254_19448.range);
        curmodule = (uu___254_19448.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___254_19448.gamma_sig);
        gamma_cache = (uu___254_19448.gamma_cache);
        modules = (uu___254_19448.modules);
        expected_typ = (uu___254_19448.expected_typ);
        sigtab = (uu___254_19448.sigtab);
        attrtab = (uu___254_19448.attrtab);
        is_pattern = (uu___254_19448.is_pattern);
        instantiate_imp = (uu___254_19448.instantiate_imp);
        effects = (uu___254_19448.effects);
        generalize = (uu___254_19448.generalize);
        letrecs = (uu___254_19448.letrecs);
        top_level = (uu___254_19448.top_level);
        check_uvars = (uu___254_19448.check_uvars);
        use_eq = (uu___254_19448.use_eq);
        is_iface = (uu___254_19448.is_iface);
        admit = (uu___254_19448.admit);
        lax = (uu___254_19448.lax);
        lax_universes = (uu___254_19448.lax_universes);
        phase1 = (uu___254_19448.phase1);
        failhard = (uu___254_19448.failhard);
        nosynth = (uu___254_19448.nosynth);
        uvar_subtyping = (uu___254_19448.uvar_subtyping);
        tc_term = (uu___254_19448.tc_term);
        type_of = (uu___254_19448.type_of);
        universe_of = (uu___254_19448.universe_of);
        check_type_of = (uu___254_19448.check_type_of);
        use_bv_sorts = (uu___254_19448.use_bv_sorts);
        qtbl_name_and_index = (uu___254_19448.qtbl_name_and_index);
        normalized_eff_names = (uu___254_19448.normalized_eff_names);
        proof_ns = (uu___254_19448.proof_ns);
        synth_hook = (uu___254_19448.synth_hook);
        splice = (uu___254_19448.splice);
        is_native_tactic = (uu___254_19448.is_native_tactic);
        identifier_info = (uu___254_19448.identifier_info);
        tc_hooks = (uu___254_19448.tc_hooks);
        dsenv = (uu___254_19448.dsenv);
        dep_graph = (uu___254_19448.dep_graph);
        nbe = (uu___254_19448.nbe)
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
            (let uu___255_19503 = env  in
             {
               solver = (uu___255_19503.solver);
               range = (uu___255_19503.range);
               curmodule = (uu___255_19503.curmodule);
               gamma = rest;
               gamma_sig = (uu___255_19503.gamma_sig);
               gamma_cache = (uu___255_19503.gamma_cache);
               modules = (uu___255_19503.modules);
               expected_typ = (uu___255_19503.expected_typ);
               sigtab = (uu___255_19503.sigtab);
               attrtab = (uu___255_19503.attrtab);
               is_pattern = (uu___255_19503.is_pattern);
               instantiate_imp = (uu___255_19503.instantiate_imp);
               effects = (uu___255_19503.effects);
               generalize = (uu___255_19503.generalize);
               letrecs = (uu___255_19503.letrecs);
               top_level = (uu___255_19503.top_level);
               check_uvars = (uu___255_19503.check_uvars);
               use_eq = (uu___255_19503.use_eq);
               is_iface = (uu___255_19503.is_iface);
               admit = (uu___255_19503.admit);
               lax = (uu___255_19503.lax);
               lax_universes = (uu___255_19503.lax_universes);
               phase1 = (uu___255_19503.phase1);
               failhard = (uu___255_19503.failhard);
               nosynth = (uu___255_19503.nosynth);
               uvar_subtyping = (uu___255_19503.uvar_subtyping);
               tc_term = (uu___255_19503.tc_term);
               type_of = (uu___255_19503.type_of);
               universe_of = (uu___255_19503.universe_of);
               check_type_of = (uu___255_19503.check_type_of);
               use_bv_sorts = (uu___255_19503.use_bv_sorts);
               qtbl_name_and_index = (uu___255_19503.qtbl_name_and_index);
               normalized_eff_names = (uu___255_19503.normalized_eff_names);
               proof_ns = (uu___255_19503.proof_ns);
               synth_hook = (uu___255_19503.synth_hook);
               splice = (uu___255_19503.splice);
               is_native_tactic = (uu___255_19503.is_native_tactic);
               identifier_info = (uu___255_19503.identifier_info);
               tc_hooks = (uu___255_19503.tc_hooks);
               dsenv = (uu___255_19503.dsenv);
               dep_graph = (uu___255_19503.dep_graph);
               nbe = (uu___255_19503.nbe)
             }))
    | uu____19504 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19532  ->
             match uu____19532 with | (x,uu____19540) -> push_bv env1 x) env
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
            let uu___256_19574 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___256_19574.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___256_19574.FStar_Syntax_Syntax.index);
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
      (let uu___257_19614 = env  in
       {
         solver = (uu___257_19614.solver);
         range = (uu___257_19614.range);
         curmodule = (uu___257_19614.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_19614.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___257_19614.sigtab);
         attrtab = (uu___257_19614.attrtab);
         is_pattern = (uu___257_19614.is_pattern);
         instantiate_imp = (uu___257_19614.instantiate_imp);
         effects = (uu___257_19614.effects);
         generalize = (uu___257_19614.generalize);
         letrecs = (uu___257_19614.letrecs);
         top_level = (uu___257_19614.top_level);
         check_uvars = (uu___257_19614.check_uvars);
         use_eq = (uu___257_19614.use_eq);
         is_iface = (uu___257_19614.is_iface);
         admit = (uu___257_19614.admit);
         lax = (uu___257_19614.lax);
         lax_universes = (uu___257_19614.lax_universes);
         phase1 = (uu___257_19614.phase1);
         failhard = (uu___257_19614.failhard);
         nosynth = (uu___257_19614.nosynth);
         uvar_subtyping = (uu___257_19614.uvar_subtyping);
         tc_term = (uu___257_19614.tc_term);
         type_of = (uu___257_19614.type_of);
         universe_of = (uu___257_19614.universe_of);
         check_type_of = (uu___257_19614.check_type_of);
         use_bv_sorts = (uu___257_19614.use_bv_sorts);
         qtbl_name_and_index = (uu___257_19614.qtbl_name_and_index);
         normalized_eff_names = (uu___257_19614.normalized_eff_names);
         proof_ns = (uu___257_19614.proof_ns);
         synth_hook = (uu___257_19614.synth_hook);
         splice = (uu___257_19614.splice);
         is_native_tactic = (uu___257_19614.is_native_tactic);
         identifier_info = (uu___257_19614.identifier_info);
         tc_hooks = (uu___257_19614.tc_hooks);
         dsenv = (uu___257_19614.dsenv);
         dep_graph = (uu___257_19614.dep_graph);
         nbe = (uu___257_19614.nbe)
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
        let uu____19656 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19656 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19684 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19684)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___258_19699 = env  in
      {
        solver = (uu___258_19699.solver);
        range = (uu___258_19699.range);
        curmodule = (uu___258_19699.curmodule);
        gamma = (uu___258_19699.gamma);
        gamma_sig = (uu___258_19699.gamma_sig);
        gamma_cache = (uu___258_19699.gamma_cache);
        modules = (uu___258_19699.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___258_19699.sigtab);
        attrtab = (uu___258_19699.attrtab);
        is_pattern = (uu___258_19699.is_pattern);
        instantiate_imp = (uu___258_19699.instantiate_imp);
        effects = (uu___258_19699.effects);
        generalize = (uu___258_19699.generalize);
        letrecs = (uu___258_19699.letrecs);
        top_level = (uu___258_19699.top_level);
        check_uvars = (uu___258_19699.check_uvars);
        use_eq = false;
        is_iface = (uu___258_19699.is_iface);
        admit = (uu___258_19699.admit);
        lax = (uu___258_19699.lax);
        lax_universes = (uu___258_19699.lax_universes);
        phase1 = (uu___258_19699.phase1);
        failhard = (uu___258_19699.failhard);
        nosynth = (uu___258_19699.nosynth);
        uvar_subtyping = (uu___258_19699.uvar_subtyping);
        tc_term = (uu___258_19699.tc_term);
        type_of = (uu___258_19699.type_of);
        universe_of = (uu___258_19699.universe_of);
        check_type_of = (uu___258_19699.check_type_of);
        use_bv_sorts = (uu___258_19699.use_bv_sorts);
        qtbl_name_and_index = (uu___258_19699.qtbl_name_and_index);
        normalized_eff_names = (uu___258_19699.normalized_eff_names);
        proof_ns = (uu___258_19699.proof_ns);
        synth_hook = (uu___258_19699.synth_hook);
        splice = (uu___258_19699.splice);
        is_native_tactic = (uu___258_19699.is_native_tactic);
        identifier_info = (uu___258_19699.identifier_info);
        tc_hooks = (uu___258_19699.tc_hooks);
        dsenv = (uu___258_19699.dsenv);
        dep_graph = (uu___258_19699.dep_graph);
        nbe = (uu___258_19699.nbe)
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
    let uu____19727 = expected_typ env_  in
    ((let uu___259_19733 = env_  in
      {
        solver = (uu___259_19733.solver);
        range = (uu___259_19733.range);
        curmodule = (uu___259_19733.curmodule);
        gamma = (uu___259_19733.gamma);
        gamma_sig = (uu___259_19733.gamma_sig);
        gamma_cache = (uu___259_19733.gamma_cache);
        modules = (uu___259_19733.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___259_19733.sigtab);
        attrtab = (uu___259_19733.attrtab);
        is_pattern = (uu___259_19733.is_pattern);
        instantiate_imp = (uu___259_19733.instantiate_imp);
        effects = (uu___259_19733.effects);
        generalize = (uu___259_19733.generalize);
        letrecs = (uu___259_19733.letrecs);
        top_level = (uu___259_19733.top_level);
        check_uvars = (uu___259_19733.check_uvars);
        use_eq = false;
        is_iface = (uu___259_19733.is_iface);
        admit = (uu___259_19733.admit);
        lax = (uu___259_19733.lax);
        lax_universes = (uu___259_19733.lax_universes);
        phase1 = (uu___259_19733.phase1);
        failhard = (uu___259_19733.failhard);
        nosynth = (uu___259_19733.nosynth);
        uvar_subtyping = (uu___259_19733.uvar_subtyping);
        tc_term = (uu___259_19733.tc_term);
        type_of = (uu___259_19733.type_of);
        universe_of = (uu___259_19733.universe_of);
        check_type_of = (uu___259_19733.check_type_of);
        use_bv_sorts = (uu___259_19733.use_bv_sorts);
        qtbl_name_and_index = (uu___259_19733.qtbl_name_and_index);
        normalized_eff_names = (uu___259_19733.normalized_eff_names);
        proof_ns = (uu___259_19733.proof_ns);
        synth_hook = (uu___259_19733.synth_hook);
        splice = (uu___259_19733.splice);
        is_native_tactic = (uu___259_19733.is_native_tactic);
        identifier_info = (uu___259_19733.identifier_info);
        tc_hooks = (uu___259_19733.tc_hooks);
        dsenv = (uu___259_19733.dsenv);
        dep_graph = (uu___259_19733.dep_graph);
        nbe = (uu___259_19733.nbe)
      }), uu____19727)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19743 =
      let uu____19746 = FStar_Ident.id_of_text ""  in [uu____19746]  in
    FStar_Ident.lid_of_ids uu____19743  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19752 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19752
        then
          let uu____19755 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19755 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___260_19782 = env  in
       {
         solver = (uu___260_19782.solver);
         range = (uu___260_19782.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___260_19782.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___260_19782.expected_typ);
         sigtab = (uu___260_19782.sigtab);
         attrtab = (uu___260_19782.attrtab);
         is_pattern = (uu___260_19782.is_pattern);
         instantiate_imp = (uu___260_19782.instantiate_imp);
         effects = (uu___260_19782.effects);
         generalize = (uu___260_19782.generalize);
         letrecs = (uu___260_19782.letrecs);
         top_level = (uu___260_19782.top_level);
         check_uvars = (uu___260_19782.check_uvars);
         use_eq = (uu___260_19782.use_eq);
         is_iface = (uu___260_19782.is_iface);
         admit = (uu___260_19782.admit);
         lax = (uu___260_19782.lax);
         lax_universes = (uu___260_19782.lax_universes);
         phase1 = (uu___260_19782.phase1);
         failhard = (uu___260_19782.failhard);
         nosynth = (uu___260_19782.nosynth);
         uvar_subtyping = (uu___260_19782.uvar_subtyping);
         tc_term = (uu___260_19782.tc_term);
         type_of = (uu___260_19782.type_of);
         universe_of = (uu___260_19782.universe_of);
         check_type_of = (uu___260_19782.check_type_of);
         use_bv_sorts = (uu___260_19782.use_bv_sorts);
         qtbl_name_and_index = (uu___260_19782.qtbl_name_and_index);
         normalized_eff_names = (uu___260_19782.normalized_eff_names);
         proof_ns = (uu___260_19782.proof_ns);
         synth_hook = (uu___260_19782.synth_hook);
         splice = (uu___260_19782.splice);
         is_native_tactic = (uu___260_19782.is_native_tactic);
         identifier_info = (uu___260_19782.identifier_info);
         tc_hooks = (uu___260_19782.tc_hooks);
         dsenv = (uu___260_19782.dsenv);
         dep_graph = (uu___260_19782.dep_graph);
         nbe = (uu___260_19782.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19833)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19837,(uu____19838,t)))::tl1
          ->
          let uu____19859 =
            let uu____19862 = FStar_Syntax_Free.uvars t  in
            ext out uu____19862  in
          aux uu____19859 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19865;
            FStar_Syntax_Syntax.index = uu____19866;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19873 =
            let uu____19876 = FStar_Syntax_Free.uvars t  in
            ext out uu____19876  in
          aux uu____19873 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19933)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19937,(uu____19938,t)))::tl1
          ->
          let uu____19959 =
            let uu____19962 = FStar_Syntax_Free.univs t  in
            ext out uu____19962  in
          aux uu____19959 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19965;
            FStar_Syntax_Syntax.index = uu____19966;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19973 =
            let uu____19976 = FStar_Syntax_Free.univs t  in
            ext out uu____19976  in
          aux uu____19973 tl1
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
          let uu____20037 = FStar_Util.set_add uname out  in
          aux uu____20037 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20040,(uu____20041,t)))::tl1
          ->
          let uu____20062 =
            let uu____20065 = FStar_Syntax_Free.univnames t  in
            ext out uu____20065  in
          aux uu____20062 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20068;
            FStar_Syntax_Syntax.index = uu____20069;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20076 =
            let uu____20079 = FStar_Syntax_Free.univnames t  in
            ext out uu____20079  in
          aux uu____20076 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___234_20099  ->
            match uu___234_20099 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20103 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20116 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20126 =
      let uu____20135 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20135
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20126 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20179 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___235_20189  ->
              match uu___235_20189 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20191 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20191
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20194) ->
                  let uu____20211 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20211))
       in
    FStar_All.pipe_right uu____20179 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___236_20218  ->
    match uu___236_20218 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20220 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20220
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20240  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20282) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20301,uu____20302) -> false  in
      let uu____20311 =
        FStar_List.tryFind
          (fun uu____20329  ->
             match uu____20329 with | (p,uu____20337) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20311 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20348,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20370 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20370
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___261_20388 = e  in
        {
          solver = (uu___261_20388.solver);
          range = (uu___261_20388.range);
          curmodule = (uu___261_20388.curmodule);
          gamma = (uu___261_20388.gamma);
          gamma_sig = (uu___261_20388.gamma_sig);
          gamma_cache = (uu___261_20388.gamma_cache);
          modules = (uu___261_20388.modules);
          expected_typ = (uu___261_20388.expected_typ);
          sigtab = (uu___261_20388.sigtab);
          attrtab = (uu___261_20388.attrtab);
          is_pattern = (uu___261_20388.is_pattern);
          instantiate_imp = (uu___261_20388.instantiate_imp);
          effects = (uu___261_20388.effects);
          generalize = (uu___261_20388.generalize);
          letrecs = (uu___261_20388.letrecs);
          top_level = (uu___261_20388.top_level);
          check_uvars = (uu___261_20388.check_uvars);
          use_eq = (uu___261_20388.use_eq);
          is_iface = (uu___261_20388.is_iface);
          admit = (uu___261_20388.admit);
          lax = (uu___261_20388.lax);
          lax_universes = (uu___261_20388.lax_universes);
          phase1 = (uu___261_20388.phase1);
          failhard = (uu___261_20388.failhard);
          nosynth = (uu___261_20388.nosynth);
          uvar_subtyping = (uu___261_20388.uvar_subtyping);
          tc_term = (uu___261_20388.tc_term);
          type_of = (uu___261_20388.type_of);
          universe_of = (uu___261_20388.universe_of);
          check_type_of = (uu___261_20388.check_type_of);
          use_bv_sorts = (uu___261_20388.use_bv_sorts);
          qtbl_name_and_index = (uu___261_20388.qtbl_name_and_index);
          normalized_eff_names = (uu___261_20388.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___261_20388.synth_hook);
          splice = (uu___261_20388.splice);
          is_native_tactic = (uu___261_20388.is_native_tactic);
          identifier_info = (uu___261_20388.identifier_info);
          tc_hooks = (uu___261_20388.tc_hooks);
          dsenv = (uu___261_20388.dsenv);
          dep_graph = (uu___261_20388.dep_graph);
          nbe = (uu___261_20388.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___262_20428 = e  in
      {
        solver = (uu___262_20428.solver);
        range = (uu___262_20428.range);
        curmodule = (uu___262_20428.curmodule);
        gamma = (uu___262_20428.gamma);
        gamma_sig = (uu___262_20428.gamma_sig);
        gamma_cache = (uu___262_20428.gamma_cache);
        modules = (uu___262_20428.modules);
        expected_typ = (uu___262_20428.expected_typ);
        sigtab = (uu___262_20428.sigtab);
        attrtab = (uu___262_20428.attrtab);
        is_pattern = (uu___262_20428.is_pattern);
        instantiate_imp = (uu___262_20428.instantiate_imp);
        effects = (uu___262_20428.effects);
        generalize = (uu___262_20428.generalize);
        letrecs = (uu___262_20428.letrecs);
        top_level = (uu___262_20428.top_level);
        check_uvars = (uu___262_20428.check_uvars);
        use_eq = (uu___262_20428.use_eq);
        is_iface = (uu___262_20428.is_iface);
        admit = (uu___262_20428.admit);
        lax = (uu___262_20428.lax);
        lax_universes = (uu___262_20428.lax_universes);
        phase1 = (uu___262_20428.phase1);
        failhard = (uu___262_20428.failhard);
        nosynth = (uu___262_20428.nosynth);
        uvar_subtyping = (uu___262_20428.uvar_subtyping);
        tc_term = (uu___262_20428.tc_term);
        type_of = (uu___262_20428.type_of);
        universe_of = (uu___262_20428.universe_of);
        check_type_of = (uu___262_20428.check_type_of);
        use_bv_sorts = (uu___262_20428.use_bv_sorts);
        qtbl_name_and_index = (uu___262_20428.qtbl_name_and_index);
        normalized_eff_names = (uu___262_20428.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___262_20428.synth_hook);
        splice = (uu___262_20428.splice);
        is_native_tactic = (uu___262_20428.is_native_tactic);
        identifier_info = (uu___262_20428.identifier_info);
        tc_hooks = (uu___262_20428.tc_hooks);
        dsenv = (uu___262_20428.dsenv);
        dep_graph = (uu___262_20428.dep_graph);
        nbe = (uu___262_20428.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20443 = FStar_Syntax_Free.names t  in
      let uu____20446 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20443 uu____20446
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20467 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20467
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20475 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20475
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20492 =
      match uu____20492 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20502 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20502)
       in
    let uu____20504 =
      let uu____20507 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20507 FStar_List.rev  in
    FStar_All.pipe_right uu____20504 (FStar_String.concat " ")
  
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
                  (let uu____20560 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20560 with
                   | FStar_Pervasives_Native.Some uu____20563 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20564 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20570;
        univ_ineqs = uu____20571; implicits = uu____20572;_} -> true
    | uu____20583 -> false
  
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
          let uu___263_20610 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___263_20610.deferred);
            univ_ineqs = (uu___263_20610.univ_ineqs);
            implicits = (uu___263_20610.implicits)
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
          let uu____20645 = FStar_Options.defensive ()  in
          if uu____20645
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20649 =
              let uu____20650 =
                let uu____20651 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20651  in
              Prims.op_Negation uu____20650  in
            (if uu____20649
             then
               let uu____20656 =
                 let uu____20661 =
                   let uu____20662 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20663 =
                     let uu____20664 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20664
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20662 uu____20663
                    in
                 (FStar_Errors.Warning_Defensive, uu____20661)  in
               FStar_Errors.log_issue rng uu____20656
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
          let uu____20695 =
            let uu____20696 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20696  in
          if uu____20695
          then ()
          else
            (let uu____20698 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20698 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20721 =
            let uu____20722 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20722  in
          if uu____20721
          then ()
          else
            (let uu____20724 = bound_vars e  in
             def_check_closed_in rng msg uu____20724 t)
  
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
          let uu___264_20759 = g  in
          let uu____20760 =
            let uu____20761 =
              let uu____20762 =
                let uu____20769 =
                  let uu____20770 =
                    let uu____20787 =
                      let uu____20798 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20798]  in
                    (f, uu____20787)  in
                  FStar_Syntax_Syntax.Tm_app uu____20770  in
                FStar_Syntax_Syntax.mk uu____20769  in
              uu____20762 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20761
             in
          {
            guard_f = uu____20760;
            deferred = (uu___264_20759.deferred);
            univ_ineqs = (uu___264_20759.univ_ineqs);
            implicits = (uu___264_20759.implicits)
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
          let uu___265_20854 = g  in
          let uu____20855 =
            let uu____20856 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20856  in
          {
            guard_f = uu____20855;
            deferred = (uu___265_20854.deferred);
            univ_ineqs = (uu___265_20854.univ_ineqs);
            implicits = (uu___265_20854.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___266_20872 = g  in
          let uu____20873 =
            let uu____20874 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____20874  in
          {
            guard_f = uu____20873;
            deferred = (uu___266_20872.deferred);
            univ_ineqs = (uu___266_20872.univ_ineqs);
            implicits = (uu___266_20872.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___267_20876 = g  in
          let uu____20877 =
            let uu____20878 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20878  in
          {
            guard_f = uu____20877;
            deferred = (uu___267_20876.deferred);
            univ_ineqs = (uu___267_20876.univ_ineqs);
            implicits = (uu___267_20876.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20884 ->
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
          let uu____20899 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____20899
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____20905 =
      let uu____20906 = FStar_Syntax_Util.unmeta t  in
      uu____20906.FStar_Syntax_Syntax.n  in
    match uu____20905 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____20910 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____20951 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____20951;
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
                       let uu____21032 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21032
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___268_21036 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___268_21036.deferred);
              univ_ineqs = (uu___268_21036.univ_ineqs);
              implicits = (uu___268_21036.implicits)
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
               let uu____21069 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21069
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
            let uu___269_21092 = g  in
            let uu____21093 =
              let uu____21094 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21094  in
            {
              guard_f = uu____21093;
              deferred = (uu___269_21092.deferred);
              univ_ineqs = (uu___269_21092.univ_ineqs);
              implicits = (uu___269_21092.implicits)
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
            let uu____21132 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21132 with
            | FStar_Pervasives_Native.Some
                (uu____21157::(tm,uu____21159)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21223 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21241 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21241;
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
                    let uu___270_21276 = trivial_guard  in
                    {
                      guard_f = (uu___270_21276.guard_f);
                      deferred = (uu___270_21276.deferred);
                      univ_ineqs = (uu___270_21276.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21293  -> ());
    push = (fun uu____21295  -> ());
    pop = (fun uu____21297  -> ());
    snapshot =
      (fun uu____21299  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21308  -> fun uu____21309  -> ());
    encode_modul = (fun uu____21320  -> fun uu____21321  -> ());
    encode_sig = (fun uu____21324  -> fun uu____21325  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21331 =
             let uu____21338 = FStar_Options.peek ()  in (e, g, uu____21338)
              in
           [uu____21331]);
    solve = (fun uu____21354  -> fun uu____21355  -> fun uu____21356  -> ());
    finish = (fun uu____21362  -> ());
    refresh = (fun uu____21364  -> ())
  } 