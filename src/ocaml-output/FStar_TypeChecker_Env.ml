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
  fv_delta_depths: FStar_Syntax_Syntax.delta_depth FStar_Util.smap ;
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__solver
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__range
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__curmodule
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__gamma
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__gamma_sig
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__gamma_cache
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__modules
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__expected_typ
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__sigtab
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__attrtab
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__is_pattern
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__instantiate_imp
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__effects
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__generalize
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__letrecs
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__top_level
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__check_uvars
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__use_eq
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__is_iface
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__admit
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__lax
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__lax_universes
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__phase1
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__failhard
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__nosynth
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__uvar_subtyping
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__tc_term
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__type_of
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__universe_of
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__check_type_of
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__use_bv_sorts
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__qtbl_name_and_index
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__fv_delta_depths
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__proof_ns
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__synth_hook
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__splice
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__is_native_tactic
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__identifier_info
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__tc_hooks
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__dsenv
  
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__nbe
  
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
           (fun uu___226_9955  ->
              match uu___226_9955 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9958 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9958  in
                  let uu____9959 =
                    let uu____9960 = FStar_Syntax_Subst.compress y  in
                    uu____9960.FStar_Syntax_Syntax.n  in
                  (match uu____9959 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9964 =
                         let uu___240_9965 = y1  in
                         let uu____9966 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___240_9965.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___240_9965.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9966
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9964
                   | uu____9969 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___241_9981 = env  in
      let uu____9982 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___241_9981.solver);
        range = (uu___241_9981.range);
        curmodule = (uu___241_9981.curmodule);
        gamma = uu____9982;
        gamma_sig = (uu___241_9981.gamma_sig);
        gamma_cache = (uu___241_9981.gamma_cache);
        modules = (uu___241_9981.modules);
        expected_typ = (uu___241_9981.expected_typ);
        sigtab = (uu___241_9981.sigtab);
        attrtab = (uu___241_9981.attrtab);
        is_pattern = (uu___241_9981.is_pattern);
        instantiate_imp = (uu___241_9981.instantiate_imp);
        effects = (uu___241_9981.effects);
        generalize = (uu___241_9981.generalize);
        letrecs = (uu___241_9981.letrecs);
        top_level = (uu___241_9981.top_level);
        check_uvars = (uu___241_9981.check_uvars);
        use_eq = (uu___241_9981.use_eq);
        is_iface = (uu___241_9981.is_iface);
        admit = (uu___241_9981.admit);
        lax = (uu___241_9981.lax);
        lax_universes = (uu___241_9981.lax_universes);
        phase1 = (uu___241_9981.phase1);
        failhard = (uu___241_9981.failhard);
        nosynth = (uu___241_9981.nosynth);
        uvar_subtyping = (uu___241_9981.uvar_subtyping);
        tc_term = (uu___241_9981.tc_term);
        type_of = (uu___241_9981.type_of);
        universe_of = (uu___241_9981.universe_of);
        check_type_of = (uu___241_9981.check_type_of);
        use_bv_sorts = (uu___241_9981.use_bv_sorts);
        qtbl_name_and_index = (uu___241_9981.qtbl_name_and_index);
        normalized_eff_names = (uu___241_9981.normalized_eff_names);
        fv_delta_depths = (uu___241_9981.fv_delta_depths);
        proof_ns = (uu___241_9981.proof_ns);
        synth_hook = (uu___241_9981.synth_hook);
        splice = (uu___241_9981.splice);
        is_native_tactic = (uu___241_9981.is_native_tactic);
        identifier_info = (uu___241_9981.identifier_info);
        tc_hooks = (uu___241_9981.tc_hooks);
        dsenv = (uu___241_9981.dsenv);
        nbe = (uu___241_9981.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9989  -> fun uu____9990  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___242_10010 = env  in
      {
        solver = (uu___242_10010.solver);
        range = (uu___242_10010.range);
        curmodule = (uu___242_10010.curmodule);
        gamma = (uu___242_10010.gamma);
        gamma_sig = (uu___242_10010.gamma_sig);
        gamma_cache = (uu___242_10010.gamma_cache);
        modules = (uu___242_10010.modules);
        expected_typ = (uu___242_10010.expected_typ);
        sigtab = (uu___242_10010.sigtab);
        attrtab = (uu___242_10010.attrtab);
        is_pattern = (uu___242_10010.is_pattern);
        instantiate_imp = (uu___242_10010.instantiate_imp);
        effects = (uu___242_10010.effects);
        generalize = (uu___242_10010.generalize);
        letrecs = (uu___242_10010.letrecs);
        top_level = (uu___242_10010.top_level);
        check_uvars = (uu___242_10010.check_uvars);
        use_eq = (uu___242_10010.use_eq);
        is_iface = (uu___242_10010.is_iface);
        admit = (uu___242_10010.admit);
        lax = (uu___242_10010.lax);
        lax_universes = (uu___242_10010.lax_universes);
        phase1 = (uu___242_10010.phase1);
        failhard = (uu___242_10010.failhard);
        nosynth = (uu___242_10010.nosynth);
        uvar_subtyping = (uu___242_10010.uvar_subtyping);
        tc_term = (uu___242_10010.tc_term);
        type_of = (uu___242_10010.type_of);
        universe_of = (uu___242_10010.universe_of);
        check_type_of = (uu___242_10010.check_type_of);
        use_bv_sorts = (uu___242_10010.use_bv_sorts);
        qtbl_name_and_index = (uu___242_10010.qtbl_name_and_index);
        normalized_eff_names = (uu___242_10010.normalized_eff_names);
        fv_delta_depths = (uu___242_10010.fv_delta_depths);
        proof_ns = (uu___242_10010.proof_ns);
        synth_hook = (uu___242_10010.synth_hook);
        splice = (uu___242_10010.splice);
        is_native_tactic = (uu___242_10010.is_native_tactic);
        identifier_info = (uu___242_10010.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___242_10010.dsenv);
        nbe = (uu___242_10010.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___243_10021 = e  in
      let uu____10022 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___243_10021.solver);
        range = (uu___243_10021.range);
        curmodule = (uu___243_10021.curmodule);
        gamma = (uu___243_10021.gamma);
        gamma_sig = (uu___243_10021.gamma_sig);
        gamma_cache = (uu___243_10021.gamma_cache);
        modules = (uu___243_10021.modules);
        expected_typ = (uu___243_10021.expected_typ);
        sigtab = (uu___243_10021.sigtab);
        attrtab = (uu___243_10021.attrtab);
        is_pattern = (uu___243_10021.is_pattern);
        instantiate_imp = (uu___243_10021.instantiate_imp);
        effects = (uu___243_10021.effects);
        generalize = (uu___243_10021.generalize);
        letrecs = (uu___243_10021.letrecs);
        top_level = (uu___243_10021.top_level);
        check_uvars = (uu___243_10021.check_uvars);
        use_eq = (uu___243_10021.use_eq);
        is_iface = (uu___243_10021.is_iface);
        admit = (uu___243_10021.admit);
        lax = (uu___243_10021.lax);
        lax_universes = (uu___243_10021.lax_universes);
        phase1 = (uu___243_10021.phase1);
        failhard = (uu___243_10021.failhard);
        nosynth = (uu___243_10021.nosynth);
        uvar_subtyping = (uu___243_10021.uvar_subtyping);
        tc_term = (uu___243_10021.tc_term);
        type_of = (uu___243_10021.type_of);
        universe_of = (uu___243_10021.universe_of);
        check_type_of = (uu___243_10021.check_type_of);
        use_bv_sorts = (uu___243_10021.use_bv_sorts);
        qtbl_name_and_index = (uu___243_10021.qtbl_name_and_index);
        normalized_eff_names = (uu___243_10021.normalized_eff_names);
        fv_delta_depths = (uu___243_10021.fv_delta_depths);
        proof_ns = (uu___243_10021.proof_ns);
        synth_hook = (uu___243_10021.synth_hook);
        splice = (uu___243_10021.splice);
        is_native_tactic = (uu___243_10021.is_native_tactic);
        identifier_info = (uu___243_10021.identifier_info);
        tc_hooks = (uu___243_10021.tc_hooks);
        dsenv = uu____10022;
        nbe = (uu___243_10021.nbe)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
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
      | (NoDelta ,uu____10045) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____10046,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____10047,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____10048 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____10057 . unit -> 'Auu____10057 FStar_Util.smap =
  fun uu____10064  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____10069 . unit -> 'Auu____10069 FStar_Util.smap =
  fun uu____10076  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____10210 = new_gamma_cache ()  in
                  let uu____10213 = new_sigtab ()  in
                  let uu____10216 = new_sigtab ()  in
                  let uu____10223 =
                    let uu____10236 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____10236, FStar_Pervasives_Native.None)  in
                  let uu____10251 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____10254 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____10257 = FStar_Options.using_facts_from ()  in
                  let uu____10258 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____10261 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10210;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10213;
                    attrtab = uu____10216;
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
                    qtbl_name_and_index = uu____10223;
                    normalized_eff_names = uu____10251;
                    fv_delta_depths = uu____10254;
                    proof_ns = uu____10257;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10297  -> false);
                    identifier_info = uu____10258;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10261;
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
  fun uu____10397  ->
    let uu____10398 = FStar_ST.op_Bang query_indices  in
    match uu____10398 with
    | [] -> failwith "Empty query indices!"
    | uu____10448 ->
        let uu____10457 =
          let uu____10466 =
            let uu____10473 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10473  in
          let uu____10523 = FStar_ST.op_Bang query_indices  in uu____10466 ::
            uu____10523
           in
        FStar_ST.op_Colon_Equals query_indices uu____10457
  
let (pop_query_indices : unit -> unit) =
  fun uu____10612  ->
    let uu____10613 = FStar_ST.op_Bang query_indices  in
    match uu____10613 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10728  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10758  ->
    match uu____10758 with
    | (l,n1) ->
        let uu____10765 = FStar_ST.op_Bang query_indices  in
        (match uu____10765 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10876 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10895  ->
    let uu____10896 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10896
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10969 =
       let uu____10972 = FStar_ST.op_Bang stack  in env :: uu____10972  in
     FStar_ST.op_Colon_Equals stack uu____10969);
    (let uu___244_11021 = env  in
     let uu____11022 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____11025 = FStar_Util.smap_copy (sigtab env)  in
     let uu____11028 = FStar_Util.smap_copy (attrtab env)  in
     let uu____11035 =
       let uu____11048 =
         let uu____11051 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____11051  in
       let uu____11076 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____11048, uu____11076)  in
     let uu____11117 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____11120 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____11123 =
       let uu____11126 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____11126  in
     {
       solver = (uu___244_11021.solver);
       range = (uu___244_11021.range);
       curmodule = (uu___244_11021.curmodule);
       gamma = (uu___244_11021.gamma);
       gamma_sig = (uu___244_11021.gamma_sig);
       gamma_cache = uu____11022;
       modules = (uu___244_11021.modules);
       expected_typ = (uu___244_11021.expected_typ);
       sigtab = uu____11025;
       attrtab = uu____11028;
       is_pattern = (uu___244_11021.is_pattern);
       instantiate_imp = (uu___244_11021.instantiate_imp);
       effects = (uu___244_11021.effects);
       generalize = (uu___244_11021.generalize);
       letrecs = (uu___244_11021.letrecs);
       top_level = (uu___244_11021.top_level);
       check_uvars = (uu___244_11021.check_uvars);
       use_eq = (uu___244_11021.use_eq);
       is_iface = (uu___244_11021.is_iface);
       admit = (uu___244_11021.admit);
       lax = (uu___244_11021.lax);
       lax_universes = (uu___244_11021.lax_universes);
       phase1 = (uu___244_11021.phase1);
       failhard = (uu___244_11021.failhard);
       nosynth = (uu___244_11021.nosynth);
       uvar_subtyping = (uu___244_11021.uvar_subtyping);
       tc_term = (uu___244_11021.tc_term);
       type_of = (uu___244_11021.type_of);
       universe_of = (uu___244_11021.universe_of);
       check_type_of = (uu___244_11021.check_type_of);
       use_bv_sorts = (uu___244_11021.use_bv_sorts);
       qtbl_name_and_index = uu____11035;
       normalized_eff_names = uu____11117;
       fv_delta_depths = uu____11120;
       proof_ns = (uu___244_11021.proof_ns);
       synth_hook = (uu___244_11021.synth_hook);
       splice = (uu___244_11021.splice);
       is_native_tactic = (uu___244_11021.is_native_tactic);
       identifier_info = uu____11123;
       tc_hooks = (uu___244_11021.tc_hooks);
       dsenv = (uu___244_11021.dsenv);
       nbe = (uu___244_11021.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11172  ->
    let uu____11173 = FStar_ST.op_Bang stack  in
    match uu____11173 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11227 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____11299  ->
           let uu____11300 = snapshot_stack env  in
           match uu____11300 with
           | (stack_depth,env1) ->
               let uu____11325 = snapshot_query_indices ()  in
               (match uu____11325 with
                | (query_indices_depth,()) ->
                    let uu____11349 = (env1.solver).snapshot msg  in
                    (match uu____11349 with
                     | (solver_depth,()) ->
                         let uu____11391 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11391 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___245_11437 = env1  in
                                 {
                                   solver = (uu___245_11437.solver);
                                   range = (uu___245_11437.range);
                                   curmodule = (uu___245_11437.curmodule);
                                   gamma = (uu___245_11437.gamma);
                                   gamma_sig = (uu___245_11437.gamma_sig);
                                   gamma_cache = (uu___245_11437.gamma_cache);
                                   modules = (uu___245_11437.modules);
                                   expected_typ =
                                     (uu___245_11437.expected_typ);
                                   sigtab = (uu___245_11437.sigtab);
                                   attrtab = (uu___245_11437.attrtab);
                                   is_pattern = (uu___245_11437.is_pattern);
                                   instantiate_imp =
                                     (uu___245_11437.instantiate_imp);
                                   effects = (uu___245_11437.effects);
                                   generalize = (uu___245_11437.generalize);
                                   letrecs = (uu___245_11437.letrecs);
                                   top_level = (uu___245_11437.top_level);
                                   check_uvars = (uu___245_11437.check_uvars);
                                   use_eq = (uu___245_11437.use_eq);
                                   is_iface = (uu___245_11437.is_iface);
                                   admit = (uu___245_11437.admit);
                                   lax = (uu___245_11437.lax);
                                   lax_universes =
                                     (uu___245_11437.lax_universes);
                                   phase1 = (uu___245_11437.phase1);
                                   failhard = (uu___245_11437.failhard);
                                   nosynth = (uu___245_11437.nosynth);
                                   uvar_subtyping =
                                     (uu___245_11437.uvar_subtyping);
                                   tc_term = (uu___245_11437.tc_term);
                                   type_of = (uu___245_11437.type_of);
                                   universe_of = (uu___245_11437.universe_of);
                                   check_type_of =
                                     (uu___245_11437.check_type_of);
                                   use_bv_sorts =
                                     (uu___245_11437.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___245_11437.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___245_11437.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___245_11437.fv_delta_depths);
                                   proof_ns = (uu___245_11437.proof_ns);
                                   synth_hook = (uu___245_11437.synth_hook);
                                   splice = (uu___245_11437.splice);
                                   is_native_tactic =
                                     (uu___245_11437.is_native_tactic);
                                   identifier_info =
                                     (uu___245_11437.identifier_info);
                                   tc_hooks = (uu___245_11437.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___245_11437.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11468  ->
             let uu____11469 =
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
             match uu____11469 with
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
                             ((let uu____11595 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11595
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11606 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11606
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11633,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11665 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11691  ->
                  match uu____11691 with
                  | (m,uu____11697) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11665 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___246_11705 = env  in
               {
                 solver = (uu___246_11705.solver);
                 range = (uu___246_11705.range);
                 curmodule = (uu___246_11705.curmodule);
                 gamma = (uu___246_11705.gamma);
                 gamma_sig = (uu___246_11705.gamma_sig);
                 gamma_cache = (uu___246_11705.gamma_cache);
                 modules = (uu___246_11705.modules);
                 expected_typ = (uu___246_11705.expected_typ);
                 sigtab = (uu___246_11705.sigtab);
                 attrtab = (uu___246_11705.attrtab);
                 is_pattern = (uu___246_11705.is_pattern);
                 instantiate_imp = (uu___246_11705.instantiate_imp);
                 effects = (uu___246_11705.effects);
                 generalize = (uu___246_11705.generalize);
                 letrecs = (uu___246_11705.letrecs);
                 top_level = (uu___246_11705.top_level);
                 check_uvars = (uu___246_11705.check_uvars);
                 use_eq = (uu___246_11705.use_eq);
                 is_iface = (uu___246_11705.is_iface);
                 admit = (uu___246_11705.admit);
                 lax = (uu___246_11705.lax);
                 lax_universes = (uu___246_11705.lax_universes);
                 phase1 = (uu___246_11705.phase1);
                 failhard = (uu___246_11705.failhard);
                 nosynth = (uu___246_11705.nosynth);
                 uvar_subtyping = (uu___246_11705.uvar_subtyping);
                 tc_term = (uu___246_11705.tc_term);
                 type_of = (uu___246_11705.type_of);
                 universe_of = (uu___246_11705.universe_of);
                 check_type_of = (uu___246_11705.check_type_of);
                 use_bv_sorts = (uu___246_11705.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___246_11705.normalized_eff_names);
                 fv_delta_depths = (uu___246_11705.fv_delta_depths);
                 proof_ns = (uu___246_11705.proof_ns);
                 synth_hook = (uu___246_11705.synth_hook);
                 splice = (uu___246_11705.splice);
                 is_native_tactic = (uu___246_11705.is_native_tactic);
                 identifier_info = (uu___246_11705.identifier_info);
                 tc_hooks = (uu___246_11705.tc_hooks);
                 dsenv = (uu___246_11705.dsenv);
                 nbe = (uu___246_11705.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11718,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___247_11727 = env  in
               {
                 solver = (uu___247_11727.solver);
                 range = (uu___247_11727.range);
                 curmodule = (uu___247_11727.curmodule);
                 gamma = (uu___247_11727.gamma);
                 gamma_sig = (uu___247_11727.gamma_sig);
                 gamma_cache = (uu___247_11727.gamma_cache);
                 modules = (uu___247_11727.modules);
                 expected_typ = (uu___247_11727.expected_typ);
                 sigtab = (uu___247_11727.sigtab);
                 attrtab = (uu___247_11727.attrtab);
                 is_pattern = (uu___247_11727.is_pattern);
                 instantiate_imp = (uu___247_11727.instantiate_imp);
                 effects = (uu___247_11727.effects);
                 generalize = (uu___247_11727.generalize);
                 letrecs = (uu___247_11727.letrecs);
                 top_level = (uu___247_11727.top_level);
                 check_uvars = (uu___247_11727.check_uvars);
                 use_eq = (uu___247_11727.use_eq);
                 is_iface = (uu___247_11727.is_iface);
                 admit = (uu___247_11727.admit);
                 lax = (uu___247_11727.lax);
                 lax_universes = (uu___247_11727.lax_universes);
                 phase1 = (uu___247_11727.phase1);
                 failhard = (uu___247_11727.failhard);
                 nosynth = (uu___247_11727.nosynth);
                 uvar_subtyping = (uu___247_11727.uvar_subtyping);
                 tc_term = (uu___247_11727.tc_term);
                 type_of = (uu___247_11727.type_of);
                 universe_of = (uu___247_11727.universe_of);
                 check_type_of = (uu___247_11727.check_type_of);
                 use_bv_sorts = (uu___247_11727.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___247_11727.normalized_eff_names);
                 fv_delta_depths = (uu___247_11727.fv_delta_depths);
                 proof_ns = (uu___247_11727.proof_ns);
                 synth_hook = (uu___247_11727.synth_hook);
                 splice = (uu___247_11727.splice);
                 is_native_tactic = (uu___247_11727.is_native_tactic);
                 identifier_info = (uu___247_11727.identifier_info);
                 tc_hooks = (uu___247_11727.tc_hooks);
                 dsenv = (uu___247_11727.dsenv);
                 nbe = (uu___247_11727.nbe)
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
        (let uu___248_11761 = e  in
         {
           solver = (uu___248_11761.solver);
           range = r;
           curmodule = (uu___248_11761.curmodule);
           gamma = (uu___248_11761.gamma);
           gamma_sig = (uu___248_11761.gamma_sig);
           gamma_cache = (uu___248_11761.gamma_cache);
           modules = (uu___248_11761.modules);
           expected_typ = (uu___248_11761.expected_typ);
           sigtab = (uu___248_11761.sigtab);
           attrtab = (uu___248_11761.attrtab);
           is_pattern = (uu___248_11761.is_pattern);
           instantiate_imp = (uu___248_11761.instantiate_imp);
           effects = (uu___248_11761.effects);
           generalize = (uu___248_11761.generalize);
           letrecs = (uu___248_11761.letrecs);
           top_level = (uu___248_11761.top_level);
           check_uvars = (uu___248_11761.check_uvars);
           use_eq = (uu___248_11761.use_eq);
           is_iface = (uu___248_11761.is_iface);
           admit = (uu___248_11761.admit);
           lax = (uu___248_11761.lax);
           lax_universes = (uu___248_11761.lax_universes);
           phase1 = (uu___248_11761.phase1);
           failhard = (uu___248_11761.failhard);
           nosynth = (uu___248_11761.nosynth);
           uvar_subtyping = (uu___248_11761.uvar_subtyping);
           tc_term = (uu___248_11761.tc_term);
           type_of = (uu___248_11761.type_of);
           universe_of = (uu___248_11761.universe_of);
           check_type_of = (uu___248_11761.check_type_of);
           use_bv_sorts = (uu___248_11761.use_bv_sorts);
           qtbl_name_and_index = (uu___248_11761.qtbl_name_and_index);
           normalized_eff_names = (uu___248_11761.normalized_eff_names);
           fv_delta_depths = (uu___248_11761.fv_delta_depths);
           proof_ns = (uu___248_11761.proof_ns);
           synth_hook = (uu___248_11761.synth_hook);
           splice = (uu___248_11761.splice);
           is_native_tactic = (uu___248_11761.is_native_tactic);
           identifier_info = (uu___248_11761.identifier_info);
           tc_hooks = (uu___248_11761.tc_hooks);
           dsenv = (uu___248_11761.dsenv);
           nbe = (uu___248_11761.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11777 =
        let uu____11778 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11778 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11777
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11832 =
          let uu____11833 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11833 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11832
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11887 =
          let uu____11888 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11888 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11887
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11942 =
        let uu____11943 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11943 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11942
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___249_12004 = env  in
      {
        solver = (uu___249_12004.solver);
        range = (uu___249_12004.range);
        curmodule = lid;
        gamma = (uu___249_12004.gamma);
        gamma_sig = (uu___249_12004.gamma_sig);
        gamma_cache = (uu___249_12004.gamma_cache);
        modules = (uu___249_12004.modules);
        expected_typ = (uu___249_12004.expected_typ);
        sigtab = (uu___249_12004.sigtab);
        attrtab = (uu___249_12004.attrtab);
        is_pattern = (uu___249_12004.is_pattern);
        instantiate_imp = (uu___249_12004.instantiate_imp);
        effects = (uu___249_12004.effects);
        generalize = (uu___249_12004.generalize);
        letrecs = (uu___249_12004.letrecs);
        top_level = (uu___249_12004.top_level);
        check_uvars = (uu___249_12004.check_uvars);
        use_eq = (uu___249_12004.use_eq);
        is_iface = (uu___249_12004.is_iface);
        admit = (uu___249_12004.admit);
        lax = (uu___249_12004.lax);
        lax_universes = (uu___249_12004.lax_universes);
        phase1 = (uu___249_12004.phase1);
        failhard = (uu___249_12004.failhard);
        nosynth = (uu___249_12004.nosynth);
        uvar_subtyping = (uu___249_12004.uvar_subtyping);
        tc_term = (uu___249_12004.tc_term);
        type_of = (uu___249_12004.type_of);
        universe_of = (uu___249_12004.universe_of);
        check_type_of = (uu___249_12004.check_type_of);
        use_bv_sorts = (uu___249_12004.use_bv_sorts);
        qtbl_name_and_index = (uu___249_12004.qtbl_name_and_index);
        normalized_eff_names = (uu___249_12004.normalized_eff_names);
        fv_delta_depths = (uu___249_12004.fv_delta_depths);
        proof_ns = (uu___249_12004.proof_ns);
        synth_hook = (uu___249_12004.synth_hook);
        splice = (uu___249_12004.splice);
        is_native_tactic = (uu___249_12004.is_native_tactic);
        identifier_info = (uu___249_12004.identifier_info);
        tc_hooks = (uu___249_12004.tc_hooks);
        dsenv = (uu___249_12004.dsenv);
        nbe = (uu___249_12004.nbe)
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
      let uu____12031 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____12031
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____12041 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____12041)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____12051 =
      let uu____12052 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____12052  in
    (FStar_Errors.Fatal_VariableNotFound, uu____12051)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____12057  ->
    let uu____12058 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____12058
  
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
      | ((formals,t),uu____12152) ->
          let vs = mk_univ_subst formals us  in
          let uu____12176 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12176)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___227_12192  ->
    match uu___227_12192 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12218  -> new_u_univ ()))
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
      let uu____12237 = inst_tscheme t  in
      match uu____12237 with
      | (us,t1) ->
          let uu____12248 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12248)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12268  ->
          match uu____12268 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12289 =
                         let uu____12290 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12291 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12292 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12293 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12290 uu____12291 uu____12292 uu____12293
                          in
                       failwith uu____12289)
                    else ();
                    (let uu____12295 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12295))
               | uu____12304 ->
                   let uu____12305 =
                     let uu____12306 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12306
                      in
                   failwith uu____12305)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12312 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12318 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12324 -> false
  
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
             | ([],uu____12366) -> Maybe
             | (uu____12373,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12392 -> No  in
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
          let uu____12483 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12483 with
          | FStar_Pervasives_Native.None  ->
              let uu____12506 =
                FStar_Util.find_map env.gamma
                  (fun uu___228_12550  ->
                     match uu___228_12550 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12589 = FStar_Ident.lid_equals lid l  in
                         if uu____12589
                         then
                           let uu____12610 =
                             let uu____12629 =
                               let uu____12644 = inst_tscheme t  in
                               FStar_Util.Inl uu____12644  in
                             let uu____12659 = FStar_Ident.range_of_lid l  in
                             (uu____12629, uu____12659)  in
                           FStar_Pervasives_Native.Some uu____12610
                         else FStar_Pervasives_Native.None
                     | uu____12711 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12506
                (fun uu____12749  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___229_12758  ->
                        match uu___229_12758 with
                        | (uu____12761,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12763);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12764;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12765;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12766;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12767;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12787 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12787
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
                                  uu____12835 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12842 -> cache t  in
                            let uu____12843 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12843 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12849 =
                                   let uu____12850 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12850)
                                    in
                                 maybe_cache uu____12849)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12918 = find_in_sigtab env lid  in
         match uu____12918 with
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
      let uu____12998 = lookup_qname env lid  in
      match uu____12998 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____13019,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13130 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13130 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13172 =
          let uu____13175 = lookup_attr env1 attr  in se1 :: uu____13175  in
        FStar_Util.smap_add (attrtab env1) attr uu____13172  in
      FStar_List.iter
        (fun attr  ->
           let uu____13185 =
             let uu____13186 = FStar_Syntax_Subst.compress attr  in
             uu____13186.FStar_Syntax_Syntax.n  in
           match uu____13185 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13190 =
                 let uu____13191 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13191.FStar_Ident.str  in
               add_one1 env se uu____13190
           | uu____13192 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13214) ->
          add_sigelts env ses
      | uu____13223 ->
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
            | uu____13238 -> ()))

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
        (fun uu___230_13269  ->
           match uu___230_13269 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13287 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13348,lb::[]),uu____13350) ->
            let uu____13357 =
              let uu____13366 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13375 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13366, uu____13375)  in
            FStar_Pervasives_Native.Some uu____13357
        | FStar_Syntax_Syntax.Sig_let ((uu____13388,lbs),uu____13390) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13420 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13432 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13432
                     then
                       let uu____13443 =
                         let uu____13452 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13461 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13452, uu____13461)  in
                       FStar_Pervasives_Native.Some uu____13443
                     else FStar_Pervasives_Native.None)
        | uu____13483 -> FStar_Pervasives_Native.None
  
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
          let uu____13542 =
            let uu____13551 =
              let uu____13556 =
                let uu____13557 =
                  let uu____13560 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13560
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13557)  in
              inst_tscheme1 uu____13556  in
            (uu____13551, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13542
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13582,uu____13583) ->
          let uu____13588 =
            let uu____13597 =
              let uu____13602 =
                let uu____13603 =
                  let uu____13606 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13606  in
                (us, uu____13603)  in
              inst_tscheme1 uu____13602  in
            (uu____13597, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13588
      | uu____13625 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13713 =
          match uu____13713 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13809,uvs,t,uu____13812,uu____13813,uu____13814);
                      FStar_Syntax_Syntax.sigrng = uu____13815;
                      FStar_Syntax_Syntax.sigquals = uu____13816;
                      FStar_Syntax_Syntax.sigmeta = uu____13817;
                      FStar_Syntax_Syntax.sigattrs = uu____13818;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13839 =
                     let uu____13848 = inst_tscheme1 (uvs, t)  in
                     (uu____13848, rng)  in
                   FStar_Pervasives_Native.Some uu____13839
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13872;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13874;
                      FStar_Syntax_Syntax.sigattrs = uu____13875;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13892 =
                     let uu____13893 = in_cur_mod env l  in uu____13893 = Yes
                      in
                   if uu____13892
                   then
                     let uu____13904 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13904
                      then
                        let uu____13917 =
                          let uu____13926 = inst_tscheme1 (uvs, t)  in
                          (uu____13926, rng)  in
                        FStar_Pervasives_Native.Some uu____13917
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13957 =
                        let uu____13966 = inst_tscheme1 (uvs, t)  in
                        (uu____13966, rng)  in
                      FStar_Pervasives_Native.Some uu____13957)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13991,uu____13992);
                      FStar_Syntax_Syntax.sigrng = uu____13993;
                      FStar_Syntax_Syntax.sigquals = uu____13994;
                      FStar_Syntax_Syntax.sigmeta = uu____13995;
                      FStar_Syntax_Syntax.sigattrs = uu____13996;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____14037 =
                          let uu____14046 = inst_tscheme1 (uvs, k)  in
                          (uu____14046, rng)  in
                        FStar_Pervasives_Native.Some uu____14037
                    | uu____14067 ->
                        let uu____14068 =
                          let uu____14077 =
                            let uu____14082 =
                              let uu____14083 =
                                let uu____14086 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14086
                                 in
                              (uvs, uu____14083)  in
                            inst_tscheme1 uu____14082  in
                          (uu____14077, rng)  in
                        FStar_Pervasives_Native.Some uu____14068)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14109,uu____14110);
                      FStar_Syntax_Syntax.sigrng = uu____14111;
                      FStar_Syntax_Syntax.sigquals = uu____14112;
                      FStar_Syntax_Syntax.sigmeta = uu____14113;
                      FStar_Syntax_Syntax.sigattrs = uu____14114;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14156 =
                          let uu____14165 = inst_tscheme_with (uvs, k) us  in
                          (uu____14165, rng)  in
                        FStar_Pervasives_Native.Some uu____14156
                    | uu____14186 ->
                        let uu____14187 =
                          let uu____14196 =
                            let uu____14201 =
                              let uu____14202 =
                                let uu____14205 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14205
                                 in
                              (uvs, uu____14202)  in
                            inst_tscheme_with uu____14201 us  in
                          (uu____14196, rng)  in
                        FStar_Pervasives_Native.Some uu____14187)
               | FStar_Util.Inr se ->
                   let uu____14241 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14262;
                          FStar_Syntax_Syntax.sigrng = uu____14263;
                          FStar_Syntax_Syntax.sigquals = uu____14264;
                          FStar_Syntax_Syntax.sigmeta = uu____14265;
                          FStar_Syntax_Syntax.sigattrs = uu____14266;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14281 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14241
                     (FStar_Util.map_option
                        (fun uu____14329  ->
                           match uu____14329 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14360 =
          let uu____14371 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14371 mapper  in
        match uu____14360 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14445 =
              let uu____14456 =
                let uu____14463 =
                  let uu___250_14466 = t  in
                  let uu____14467 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___250_14466.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14467;
                    FStar_Syntax_Syntax.vars =
                      (uu___250_14466.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14463)  in
              (uu____14456, r)  in
            FStar_Pervasives_Native.Some uu____14445
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14514 = lookup_qname env l  in
      match uu____14514 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14533 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14585 = try_lookup_bv env bv  in
      match uu____14585 with
      | FStar_Pervasives_Native.None  ->
          let uu____14600 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14600 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14615 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14616 =
            let uu____14617 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14617  in
          (uu____14615, uu____14616)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14638 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14638 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14704 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14704  in
          let uu____14705 =
            let uu____14714 =
              let uu____14719 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14719)  in
            (uu____14714, r1)  in
          FStar_Pervasives_Native.Some uu____14705
  
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
        let uu____14753 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14753 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14786,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14811 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14811  in
            let uu____14812 =
              let uu____14817 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14817, r1)  in
            FStar_Pervasives_Native.Some uu____14812
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14840 = try_lookup_lid env l  in
      match uu____14840 with
      | FStar_Pervasives_Native.None  ->
          let uu____14867 = name_not_found l  in
          let uu____14872 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14867 uu____14872
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___231_14912  ->
              match uu___231_14912 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14914 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14933 = lookup_qname env lid  in
      match uu____14933 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14942,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14945;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14947;
              FStar_Syntax_Syntax.sigattrs = uu____14948;_},FStar_Pervasives_Native.None
            ),uu____14949)
          ->
          let uu____14998 =
            let uu____15005 =
              let uu____15006 =
                let uu____15009 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____15009 t  in
              (uvs, uu____15006)  in
            (uu____15005, q)  in
          FStar_Pervasives_Native.Some uu____14998
      | uu____15022 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15043 = lookup_qname env lid  in
      match uu____15043 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15048,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15051;
              FStar_Syntax_Syntax.sigquals = uu____15052;
              FStar_Syntax_Syntax.sigmeta = uu____15053;
              FStar_Syntax_Syntax.sigattrs = uu____15054;_},FStar_Pervasives_Native.None
            ),uu____15055)
          ->
          let uu____15104 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15104 (uvs, t)
      | uu____15109 ->
          let uu____15110 = name_not_found lid  in
          let uu____15115 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15110 uu____15115
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15134 = lookup_qname env lid  in
      match uu____15134 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15139,uvs,t,uu____15142,uu____15143,uu____15144);
              FStar_Syntax_Syntax.sigrng = uu____15145;
              FStar_Syntax_Syntax.sigquals = uu____15146;
              FStar_Syntax_Syntax.sigmeta = uu____15147;
              FStar_Syntax_Syntax.sigattrs = uu____15148;_},FStar_Pervasives_Native.None
            ),uu____15149)
          ->
          let uu____15202 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15202 (uvs, t)
      | uu____15207 ->
          let uu____15208 = name_not_found lid  in
          let uu____15213 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15208 uu____15213
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15234 = lookup_qname env lid  in
      match uu____15234 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15241,uu____15242,uu____15243,uu____15244,uu____15245,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15247;
              FStar_Syntax_Syntax.sigquals = uu____15248;
              FStar_Syntax_Syntax.sigmeta = uu____15249;
              FStar_Syntax_Syntax.sigattrs = uu____15250;_},uu____15251),uu____15252)
          -> (true, dcs)
      | uu____15313 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15326 = lookup_qname env lid  in
      match uu____15326 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15327,uu____15328,uu____15329,l,uu____15331,uu____15332);
              FStar_Syntax_Syntax.sigrng = uu____15333;
              FStar_Syntax_Syntax.sigquals = uu____15334;
              FStar_Syntax_Syntax.sigmeta = uu____15335;
              FStar_Syntax_Syntax.sigattrs = uu____15336;_},uu____15337),uu____15338)
          -> l
      | uu____15393 ->
          let uu____15394 =
            let uu____15395 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15395  in
          failwith uu____15394
  
let (lookup_definition_qninfo_aux :
  Prims.bool ->
    delta_level Prims.list ->
      FStar_Ident.lident ->
        qninfo ->
          (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                      FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun rec_ok  ->
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15457)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____15514) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____15536 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____15536
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____15568 -> FStar_Pervasives_Native.None)
          | uu____15577 -> FStar_Pervasives_Native.None
  
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
        lookup_definition_qninfo_aux true delta_levels lid qninfo
  
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
        let uu____15636 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15636
  
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____15668 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____15668
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____15713,uu____15714) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____15762),uu____15763) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____15812 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____15829 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____15838 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____15853 ->
                  let uu____15860 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____15860
              | FStar_Syntax_Syntax.Sig_let ((uu____15861,lbs),uu____15863)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____15877 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____15877
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____15881 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____15888 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____15889 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____15896 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15897 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____15898 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15899 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____15912 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____15925 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____15925
           (fun d_opt  ->
              let uu____15937 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____15937
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____15943 =
                   let uu____15946 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____15946  in
                 match uu____15943 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____15947 =
                       let uu____15948 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____15948
                        in
                     failwith uu____15947
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____15951 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____15951
                       then
                         let uu____15952 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____15953 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____15954 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____15952 uu____15953 uu____15954
                       else ());
                      FStar_Util.smap_add env.fv_delta_depths
                        lid.FStar_Ident.str d;
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15975),uu____15976) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____16025 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____16046),uu____16047) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____16096 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____16117 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____16117
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____16136 = lookup_qname env ftv  in
      match uu____16136 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____16140) ->
          let uu____16185 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____16185 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____16206,t),r) ->
               let uu____16221 =
                 let uu____16222 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____16222 t  in
               FStar_Pervasives_Native.Some uu____16221)
      | uu____16223 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____16234 = try_lookup_effect_lid env ftv  in
      match uu____16234 with
      | FStar_Pervasives_Native.None  ->
          let uu____16237 = name_not_found ftv  in
          let uu____16242 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____16237 uu____16242
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
        let uu____16265 = lookup_qname env lid0  in
        match uu____16265 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____16276);
                FStar_Syntax_Syntax.sigrng = uu____16277;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____16279;
                FStar_Syntax_Syntax.sigattrs = uu____16280;_},FStar_Pervasives_Native.None
              ),uu____16281)
            ->
            let lid1 =
              let uu____16335 =
                let uu____16336 = FStar_Ident.range_of_lid lid  in
                let uu____16337 =
                  let uu____16338 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____16338  in
                FStar_Range.set_use_range uu____16336 uu____16337  in
              FStar_Ident.set_lid_range lid uu____16335  in
            let uu____16339 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___232_16343  ->
                      match uu___232_16343 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____16344 -> false))
               in
            if uu____16339
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____16358 =
                      let uu____16359 =
                        let uu____16360 = get_range env  in
                        FStar_Range.string_of_range uu____16360  in
                      let uu____16361 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____16362 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____16359 uu____16361 uu____16362
                       in
                    failwith uu____16358)
                  in
               match (binders, univs1) with
               | ([],uu____16379) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16404,uu____16405::uu____16406::uu____16407) ->
                   let uu____16428 =
                     let uu____16429 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____16430 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16429 uu____16430
                      in
                   failwith uu____16428
               | uu____16437 ->
                   let uu____16452 =
                     let uu____16457 =
                       let uu____16458 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____16458)  in
                     inst_tscheme_with uu____16457 insts  in
                   (match uu____16452 with
                    | (uu____16471,t) ->
                        let t1 =
                          let uu____16474 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16474 t  in
                        let uu____16475 =
                          let uu____16476 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16476.FStar_Syntax_Syntax.n  in
                        (match uu____16475 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16511 -> failwith "Impossible")))
        | uu____16518 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16541 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16541 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16554,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16561 = find1 l2  in
            (match uu____16561 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16568 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16568 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16572 = find1 l  in
            (match uu____16572 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16577 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16577
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16591 = lookup_qname env l1  in
      match uu____16591 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16594;
              FStar_Syntax_Syntax.sigrng = uu____16595;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16597;
              FStar_Syntax_Syntax.sigattrs = uu____16598;_},uu____16599),uu____16600)
          -> q
      | uu____16651 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16672 =
          let uu____16673 =
            let uu____16674 = FStar_Util.string_of_int i  in
            let uu____16675 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16674 uu____16675
             in
          failwith uu____16673  in
        let uu____16676 = lookup_datacon env lid  in
        match uu____16676 with
        | (uu____16681,t) ->
            let uu____16683 =
              let uu____16684 = FStar_Syntax_Subst.compress t  in
              uu____16684.FStar_Syntax_Syntax.n  in
            (match uu____16683 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16688) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16729 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16729
                      FStar_Pervasives_Native.fst)
             | uu____16740 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16751 = lookup_qname env l  in
      match uu____16751 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16752,uu____16753,uu____16754);
              FStar_Syntax_Syntax.sigrng = uu____16755;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16757;
              FStar_Syntax_Syntax.sigattrs = uu____16758;_},uu____16759),uu____16760)
          ->
          FStar_Util.for_some
            (fun uu___233_16813  ->
               match uu___233_16813 with
               | FStar_Syntax_Syntax.Projector uu____16814 -> true
               | uu____16819 -> false) quals
      | uu____16820 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16831 = lookup_qname env lid  in
      match uu____16831 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16832,uu____16833,uu____16834,uu____16835,uu____16836,uu____16837);
              FStar_Syntax_Syntax.sigrng = uu____16838;
              FStar_Syntax_Syntax.sigquals = uu____16839;
              FStar_Syntax_Syntax.sigmeta = uu____16840;
              FStar_Syntax_Syntax.sigattrs = uu____16841;_},uu____16842),uu____16843)
          -> true
      | uu____16898 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16909 = lookup_qname env lid  in
      match uu____16909 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16910,uu____16911,uu____16912,uu____16913,uu____16914,uu____16915);
              FStar_Syntax_Syntax.sigrng = uu____16916;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16918;
              FStar_Syntax_Syntax.sigattrs = uu____16919;_},uu____16920),uu____16921)
          ->
          FStar_Util.for_some
            (fun uu___234_16982  ->
               match uu___234_16982 with
               | FStar_Syntax_Syntax.RecordType uu____16983 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16992 -> true
               | uu____17001 -> false) quals
      | uu____17002 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____17008,uu____17009);
            FStar_Syntax_Syntax.sigrng = uu____17010;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____17012;
            FStar_Syntax_Syntax.sigattrs = uu____17013;_},uu____17014),uu____17015)
        ->
        FStar_Util.for_some
          (fun uu___235_17072  ->
             match uu___235_17072 with
             | FStar_Syntax_Syntax.Action uu____17073 -> true
             | uu____17074 -> false) quals
    | uu____17075 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17086 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____17086
  
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
      let uu____17100 =
        let uu____17101 = FStar_Syntax_Util.un_uinst head1  in
        uu____17101.FStar_Syntax_Syntax.n  in
      match uu____17100 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____17105 ->
               true
           | uu____17106 -> false)
      | uu____17107 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17118 = lookup_qname env l  in
      match uu____17118 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____17120),uu____17121) ->
          FStar_Util.for_some
            (fun uu___236_17169  ->
               match uu___236_17169 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____17170 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____17171 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____17242 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____17258) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____17275 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____17282 ->
                 FStar_Pervasives_Native.Some true
             | uu____17299 -> FStar_Pervasives_Native.Some false)
         in
      let uu____17300 =
        let uu____17303 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____17303 mapper  in
      match uu____17300 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____17355 = lookup_qname env lid  in
      match uu____17355 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17358,uu____17359,tps,uu____17361,uu____17362,uu____17363);
              FStar_Syntax_Syntax.sigrng = uu____17364;
              FStar_Syntax_Syntax.sigquals = uu____17365;
              FStar_Syntax_Syntax.sigmeta = uu____17366;
              FStar_Syntax_Syntax.sigattrs = uu____17367;_},uu____17368),uu____17369)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____17434 -> FStar_Pervasives_Native.None
  
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
           (fun uu____17478  ->
              match uu____17478 with
              | (d,uu____17486) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17501 = effect_decl_opt env l  in
      match uu____17501 with
      | FStar_Pervasives_Native.None  ->
          let uu____17516 = name_not_found l  in
          let uu____17521 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17516 uu____17521
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17543  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17562  ->
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
        let uu____17593 = FStar_Ident.lid_equals l1 l2  in
        if uu____17593
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17601 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17601
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17609 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17662  ->
                        match uu____17662 with
                        | (m1,m2,uu____17675,uu____17676,uu____17677) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17609 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17694 =
                    let uu____17699 =
                      let uu____17700 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17701 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17700
                        uu____17701
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17699)
                     in
                  FStar_Errors.raise_error uu____17694 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17708,uu____17709,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17742 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17742
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
  'Auu____17758 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17758)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17787 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17813  ->
                match uu____17813 with
                | (d,uu____17819) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17787 with
      | FStar_Pervasives_Native.None  ->
          let uu____17830 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17830
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17843 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17843 with
           | (uu____17858,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17876)::(wp,uu____17878)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17934 -> failwith "Impossible"))
  
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
          let uu____17989 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17989
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17991 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17991
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
                  let uu____17999 = get_range env  in
                  let uu____18000 =
                    let uu____18007 =
                      let uu____18008 =
                        let uu____18025 =
                          let uu____18036 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____18036]  in
                        (null_wp, uu____18025)  in
                      FStar_Syntax_Syntax.Tm_app uu____18008  in
                    FStar_Syntax_Syntax.mk uu____18007  in
                  uu____18000 FStar_Pervasives_Native.None uu____17999  in
                let uu____18076 =
                  let uu____18077 =
                    let uu____18088 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____18088]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____18077;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____18076))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___251_18125 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___251_18125.order);
              joins = (uu___251_18125.joins)
            }  in
          let uu___252_18134 = env  in
          {
            solver = (uu___252_18134.solver);
            range = (uu___252_18134.range);
            curmodule = (uu___252_18134.curmodule);
            gamma = (uu___252_18134.gamma);
            gamma_sig = (uu___252_18134.gamma_sig);
            gamma_cache = (uu___252_18134.gamma_cache);
            modules = (uu___252_18134.modules);
            expected_typ = (uu___252_18134.expected_typ);
            sigtab = (uu___252_18134.sigtab);
            attrtab = (uu___252_18134.attrtab);
            is_pattern = (uu___252_18134.is_pattern);
            instantiate_imp = (uu___252_18134.instantiate_imp);
            effects;
            generalize = (uu___252_18134.generalize);
            letrecs = (uu___252_18134.letrecs);
            top_level = (uu___252_18134.top_level);
            check_uvars = (uu___252_18134.check_uvars);
            use_eq = (uu___252_18134.use_eq);
            is_iface = (uu___252_18134.is_iface);
            admit = (uu___252_18134.admit);
            lax = (uu___252_18134.lax);
            lax_universes = (uu___252_18134.lax_universes);
            phase1 = (uu___252_18134.phase1);
            failhard = (uu___252_18134.failhard);
            nosynth = (uu___252_18134.nosynth);
            uvar_subtyping = (uu___252_18134.uvar_subtyping);
            tc_term = (uu___252_18134.tc_term);
            type_of = (uu___252_18134.type_of);
            universe_of = (uu___252_18134.universe_of);
            check_type_of = (uu___252_18134.check_type_of);
            use_bv_sorts = (uu___252_18134.use_bv_sorts);
            qtbl_name_and_index = (uu___252_18134.qtbl_name_and_index);
            normalized_eff_names = (uu___252_18134.normalized_eff_names);
            fv_delta_depths = (uu___252_18134.fv_delta_depths);
            proof_ns = (uu___252_18134.proof_ns);
            synth_hook = (uu___252_18134.synth_hook);
            splice = (uu___252_18134.splice);
            is_native_tactic = (uu___252_18134.is_native_tactic);
            identifier_info = (uu___252_18134.identifier_info);
            tc_hooks = (uu___252_18134.tc_hooks);
            dsenv = (uu___252_18134.dsenv);
            nbe = (uu___252_18134.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____18164 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____18164  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____18322 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____18323 = l1 u t wp e  in
                                l2 u t uu____18322 uu____18323))
                | uu____18324 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____18396 = inst_tscheme_with lift_t [u]  in
            match uu____18396 with
            | (uu____18403,lift_t1) ->
                let uu____18405 =
                  let uu____18412 =
                    let uu____18413 =
                      let uu____18430 =
                        let uu____18441 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18450 =
                          let uu____18461 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18461]  in
                        uu____18441 :: uu____18450  in
                      (lift_t1, uu____18430)  in
                    FStar_Syntax_Syntax.Tm_app uu____18413  in
                  FStar_Syntax_Syntax.mk uu____18412  in
                uu____18405 FStar_Pervasives_Native.None
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
            let uu____18573 = inst_tscheme_with lift_t [u]  in
            match uu____18573 with
            | (uu____18580,lift_t1) ->
                let uu____18582 =
                  let uu____18589 =
                    let uu____18590 =
                      let uu____18607 =
                        let uu____18618 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18627 =
                          let uu____18638 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18647 =
                            let uu____18658 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18658]  in
                          uu____18638 :: uu____18647  in
                        uu____18618 :: uu____18627  in
                      (lift_t1, uu____18607)  in
                    FStar_Syntax_Syntax.Tm_app uu____18590  in
                  FStar_Syntax_Syntax.mk uu____18589  in
                uu____18582 FStar_Pervasives_Native.None
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
              let uu____18760 =
                let uu____18761 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18761
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18760  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18765 =
              let uu____18766 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18766  in
            let uu____18767 =
              let uu____18768 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18794 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18794)
                 in
              FStar_Util.dflt "none" uu____18768  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18765
              uu____18767
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18820  ->
                    match uu____18820 with
                    | (e,uu____18828) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18851 =
            match uu____18851 with
            | (i,j) ->
                let uu____18862 = FStar_Ident.lid_equals i j  in
                if uu____18862
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
              let uu____18894 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18904 = FStar_Ident.lid_equals i k  in
                        if uu____18904
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18915 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18915
                                  then []
                                  else
                                    (let uu____18919 =
                                       let uu____18928 =
                                         find_edge order1 (i, k)  in
                                       let uu____18931 =
                                         find_edge order1 (k, j)  in
                                       (uu____18928, uu____18931)  in
                                     match uu____18919 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18946 =
                                           compose_edges e1 e2  in
                                         [uu____18946]
                                     | uu____18947 -> [])))))
                 in
              FStar_List.append order1 uu____18894  in
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
                   let uu____18977 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18979 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18979
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18977
                   then
                     let uu____18984 =
                       let uu____18989 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18989)
                        in
                     let uu____18990 = get_range env  in
                     FStar_Errors.raise_error uu____18984 uu____18990
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____19067 = FStar_Ident.lid_equals i j
                                   in
                                if uu____19067
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____19116 =
                                              let uu____19125 =
                                                find_edge order2 (i, k)  in
                                              let uu____19128 =
                                                find_edge order2 (j, k)  in
                                              (uu____19125, uu____19128)  in
                                            match uu____19116 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____19170,uu____19171)
                                                     ->
                                                     let uu____19178 =
                                                       let uu____19183 =
                                                         let uu____19184 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____19184
                                                          in
                                                       let uu____19187 =
                                                         let uu____19188 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____19188
                                                          in
                                                       (uu____19183,
                                                         uu____19187)
                                                        in
                                                     (match uu____19178 with
                                                      | (true ,true ) ->
                                                          let uu____19199 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____19199
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
                                            | uu____19224 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___253_19297 = env.effects  in
              { decls = (uu___253_19297.decls); order = order2; joins }  in
            let uu___254_19298 = env  in
            {
              solver = (uu___254_19298.solver);
              range = (uu___254_19298.range);
              curmodule = (uu___254_19298.curmodule);
              gamma = (uu___254_19298.gamma);
              gamma_sig = (uu___254_19298.gamma_sig);
              gamma_cache = (uu___254_19298.gamma_cache);
              modules = (uu___254_19298.modules);
              expected_typ = (uu___254_19298.expected_typ);
              sigtab = (uu___254_19298.sigtab);
              attrtab = (uu___254_19298.attrtab);
              is_pattern = (uu___254_19298.is_pattern);
              instantiate_imp = (uu___254_19298.instantiate_imp);
              effects;
              generalize = (uu___254_19298.generalize);
              letrecs = (uu___254_19298.letrecs);
              top_level = (uu___254_19298.top_level);
              check_uvars = (uu___254_19298.check_uvars);
              use_eq = (uu___254_19298.use_eq);
              is_iface = (uu___254_19298.is_iface);
              admit = (uu___254_19298.admit);
              lax = (uu___254_19298.lax);
              lax_universes = (uu___254_19298.lax_universes);
              phase1 = (uu___254_19298.phase1);
              failhard = (uu___254_19298.failhard);
              nosynth = (uu___254_19298.nosynth);
              uvar_subtyping = (uu___254_19298.uvar_subtyping);
              tc_term = (uu___254_19298.tc_term);
              type_of = (uu___254_19298.type_of);
              universe_of = (uu___254_19298.universe_of);
              check_type_of = (uu___254_19298.check_type_of);
              use_bv_sorts = (uu___254_19298.use_bv_sorts);
              qtbl_name_and_index = (uu___254_19298.qtbl_name_and_index);
              normalized_eff_names = (uu___254_19298.normalized_eff_names);
              fv_delta_depths = (uu___254_19298.fv_delta_depths);
              proof_ns = (uu___254_19298.proof_ns);
              synth_hook = (uu___254_19298.synth_hook);
              splice = (uu___254_19298.splice);
              is_native_tactic = (uu___254_19298.is_native_tactic);
              identifier_info = (uu___254_19298.identifier_info);
              tc_hooks = (uu___254_19298.tc_hooks);
              dsenv = (uu___254_19298.dsenv);
              nbe = (uu___254_19298.nbe)
            }))
      | uu____19299 -> env
  
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
        | uu____19327 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____19339 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____19339 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____19356 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____19356 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____19378 =
                     let uu____19383 =
                       let uu____19384 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____19391 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____19400 =
                         let uu____19401 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____19401  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____19384 uu____19391 uu____19400
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____19383)
                      in
                   FStar_Errors.raise_error uu____19378
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19406 =
                     let uu____19417 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____19417 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____19454  ->
                        fun uu____19455  ->
                          match (uu____19454, uu____19455) with
                          | ((x,uu____19485),(t,uu____19487)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19406
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19518 =
                     let uu___255_19519 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___255_19519.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___255_19519.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___255_19519.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___255_19519.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19518
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____19530 .
    'Auu____19530 ->
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
          let uu____19560 = effect_decl_opt env effect_name  in
          match uu____19560 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____19599 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19622 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____19659 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____19659
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____19660 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19660
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____19674 =
                     let uu____19677 = get_range env  in
                     let uu____19678 =
                       let uu____19685 =
                         let uu____19686 =
                           let uu____19703 =
                             let uu____19714 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____19714; wp]  in
                           (repr, uu____19703)  in
                         FStar_Syntax_Syntax.Tm_app uu____19686  in
                       FStar_Syntax_Syntax.mk uu____19685  in
                     uu____19678 FStar_Pervasives_Native.None uu____19677  in
                   FStar_Pervasives_Native.Some uu____19674)
  
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
      | uu____19829 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19840 =
        let uu____19841 = FStar_Syntax_Subst.compress t  in
        uu____19841.FStar_Syntax_Syntax.n  in
      match uu____19840 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19844,c) ->
          is_reifiable_comp env c
      | uu____19866 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____19884 =
           let uu____19885 = is_reifiable_effect env l  in
           Prims.op_Negation uu____19885  in
         if uu____19884
         then
           let uu____19886 =
             let uu____19891 =
               let uu____19892 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19892
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19891)  in
           let uu____19893 = get_range env  in
           FStar_Errors.raise_error uu____19886 uu____19893
         else ());
        (let uu____19895 = effect_repr_aux true env c u_c  in
         match uu____19895 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___256_19927 = env  in
        {
          solver = (uu___256_19927.solver);
          range = (uu___256_19927.range);
          curmodule = (uu___256_19927.curmodule);
          gamma = (uu___256_19927.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___256_19927.gamma_cache);
          modules = (uu___256_19927.modules);
          expected_typ = (uu___256_19927.expected_typ);
          sigtab = (uu___256_19927.sigtab);
          attrtab = (uu___256_19927.attrtab);
          is_pattern = (uu___256_19927.is_pattern);
          instantiate_imp = (uu___256_19927.instantiate_imp);
          effects = (uu___256_19927.effects);
          generalize = (uu___256_19927.generalize);
          letrecs = (uu___256_19927.letrecs);
          top_level = (uu___256_19927.top_level);
          check_uvars = (uu___256_19927.check_uvars);
          use_eq = (uu___256_19927.use_eq);
          is_iface = (uu___256_19927.is_iface);
          admit = (uu___256_19927.admit);
          lax = (uu___256_19927.lax);
          lax_universes = (uu___256_19927.lax_universes);
          phase1 = (uu___256_19927.phase1);
          failhard = (uu___256_19927.failhard);
          nosynth = (uu___256_19927.nosynth);
          uvar_subtyping = (uu___256_19927.uvar_subtyping);
          tc_term = (uu___256_19927.tc_term);
          type_of = (uu___256_19927.type_of);
          universe_of = (uu___256_19927.universe_of);
          check_type_of = (uu___256_19927.check_type_of);
          use_bv_sorts = (uu___256_19927.use_bv_sorts);
          qtbl_name_and_index = (uu___256_19927.qtbl_name_and_index);
          normalized_eff_names = (uu___256_19927.normalized_eff_names);
          fv_delta_depths = (uu___256_19927.fv_delta_depths);
          proof_ns = (uu___256_19927.proof_ns);
          synth_hook = (uu___256_19927.synth_hook);
          splice = (uu___256_19927.splice);
          is_native_tactic = (uu___256_19927.is_native_tactic);
          identifier_info = (uu___256_19927.identifier_info);
          tc_hooks = (uu___256_19927.tc_hooks);
          dsenv = (uu___256_19927.dsenv);
          nbe = (uu___256_19927.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___257_19940 = env  in
      {
        solver = (uu___257_19940.solver);
        range = (uu___257_19940.range);
        curmodule = (uu___257_19940.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___257_19940.gamma_sig);
        gamma_cache = (uu___257_19940.gamma_cache);
        modules = (uu___257_19940.modules);
        expected_typ = (uu___257_19940.expected_typ);
        sigtab = (uu___257_19940.sigtab);
        attrtab = (uu___257_19940.attrtab);
        is_pattern = (uu___257_19940.is_pattern);
        instantiate_imp = (uu___257_19940.instantiate_imp);
        effects = (uu___257_19940.effects);
        generalize = (uu___257_19940.generalize);
        letrecs = (uu___257_19940.letrecs);
        top_level = (uu___257_19940.top_level);
        check_uvars = (uu___257_19940.check_uvars);
        use_eq = (uu___257_19940.use_eq);
        is_iface = (uu___257_19940.is_iface);
        admit = (uu___257_19940.admit);
        lax = (uu___257_19940.lax);
        lax_universes = (uu___257_19940.lax_universes);
        phase1 = (uu___257_19940.phase1);
        failhard = (uu___257_19940.failhard);
        nosynth = (uu___257_19940.nosynth);
        uvar_subtyping = (uu___257_19940.uvar_subtyping);
        tc_term = (uu___257_19940.tc_term);
        type_of = (uu___257_19940.type_of);
        universe_of = (uu___257_19940.universe_of);
        check_type_of = (uu___257_19940.check_type_of);
        use_bv_sorts = (uu___257_19940.use_bv_sorts);
        qtbl_name_and_index = (uu___257_19940.qtbl_name_and_index);
        normalized_eff_names = (uu___257_19940.normalized_eff_names);
        fv_delta_depths = (uu___257_19940.fv_delta_depths);
        proof_ns = (uu___257_19940.proof_ns);
        synth_hook = (uu___257_19940.synth_hook);
        splice = (uu___257_19940.splice);
        is_native_tactic = (uu___257_19940.is_native_tactic);
        identifier_info = (uu___257_19940.identifier_info);
        tc_hooks = (uu___257_19940.tc_hooks);
        dsenv = (uu___257_19940.dsenv);
        nbe = (uu___257_19940.nbe)
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
            (let uu___258_19995 = env  in
             {
               solver = (uu___258_19995.solver);
               range = (uu___258_19995.range);
               curmodule = (uu___258_19995.curmodule);
               gamma = rest;
               gamma_sig = (uu___258_19995.gamma_sig);
               gamma_cache = (uu___258_19995.gamma_cache);
               modules = (uu___258_19995.modules);
               expected_typ = (uu___258_19995.expected_typ);
               sigtab = (uu___258_19995.sigtab);
               attrtab = (uu___258_19995.attrtab);
               is_pattern = (uu___258_19995.is_pattern);
               instantiate_imp = (uu___258_19995.instantiate_imp);
               effects = (uu___258_19995.effects);
               generalize = (uu___258_19995.generalize);
               letrecs = (uu___258_19995.letrecs);
               top_level = (uu___258_19995.top_level);
               check_uvars = (uu___258_19995.check_uvars);
               use_eq = (uu___258_19995.use_eq);
               is_iface = (uu___258_19995.is_iface);
               admit = (uu___258_19995.admit);
               lax = (uu___258_19995.lax);
               lax_universes = (uu___258_19995.lax_universes);
               phase1 = (uu___258_19995.phase1);
               failhard = (uu___258_19995.failhard);
               nosynth = (uu___258_19995.nosynth);
               uvar_subtyping = (uu___258_19995.uvar_subtyping);
               tc_term = (uu___258_19995.tc_term);
               type_of = (uu___258_19995.type_of);
               universe_of = (uu___258_19995.universe_of);
               check_type_of = (uu___258_19995.check_type_of);
               use_bv_sorts = (uu___258_19995.use_bv_sorts);
               qtbl_name_and_index = (uu___258_19995.qtbl_name_and_index);
               normalized_eff_names = (uu___258_19995.normalized_eff_names);
               fv_delta_depths = (uu___258_19995.fv_delta_depths);
               proof_ns = (uu___258_19995.proof_ns);
               synth_hook = (uu___258_19995.synth_hook);
               splice = (uu___258_19995.splice);
               is_native_tactic = (uu___258_19995.is_native_tactic);
               identifier_info = (uu___258_19995.identifier_info);
               tc_hooks = (uu___258_19995.tc_hooks);
               dsenv = (uu___258_19995.dsenv);
               nbe = (uu___258_19995.nbe)
             }))
    | uu____19996 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____20024  ->
             match uu____20024 with | (x,uu____20032) -> push_bv env1 x) env
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
            let uu___259_20066 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___259_20066.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___259_20066.FStar_Syntax_Syntax.index);
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
      (let uu___260_20106 = env  in
       {
         solver = (uu___260_20106.solver);
         range = (uu___260_20106.range);
         curmodule = (uu___260_20106.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___260_20106.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___260_20106.sigtab);
         attrtab = (uu___260_20106.attrtab);
         is_pattern = (uu___260_20106.is_pattern);
         instantiate_imp = (uu___260_20106.instantiate_imp);
         effects = (uu___260_20106.effects);
         generalize = (uu___260_20106.generalize);
         letrecs = (uu___260_20106.letrecs);
         top_level = (uu___260_20106.top_level);
         check_uvars = (uu___260_20106.check_uvars);
         use_eq = (uu___260_20106.use_eq);
         is_iface = (uu___260_20106.is_iface);
         admit = (uu___260_20106.admit);
         lax = (uu___260_20106.lax);
         lax_universes = (uu___260_20106.lax_universes);
         phase1 = (uu___260_20106.phase1);
         failhard = (uu___260_20106.failhard);
         nosynth = (uu___260_20106.nosynth);
         uvar_subtyping = (uu___260_20106.uvar_subtyping);
         tc_term = (uu___260_20106.tc_term);
         type_of = (uu___260_20106.type_of);
         universe_of = (uu___260_20106.universe_of);
         check_type_of = (uu___260_20106.check_type_of);
         use_bv_sorts = (uu___260_20106.use_bv_sorts);
         qtbl_name_and_index = (uu___260_20106.qtbl_name_and_index);
         normalized_eff_names = (uu___260_20106.normalized_eff_names);
         fv_delta_depths = (uu___260_20106.fv_delta_depths);
         proof_ns = (uu___260_20106.proof_ns);
         synth_hook = (uu___260_20106.synth_hook);
         splice = (uu___260_20106.splice);
         is_native_tactic = (uu___260_20106.is_native_tactic);
         identifier_info = (uu___260_20106.identifier_info);
         tc_hooks = (uu___260_20106.tc_hooks);
         dsenv = (uu___260_20106.dsenv);
         nbe = (uu___260_20106.nbe)
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
        let uu____20148 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____20148 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____20176 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____20176)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___261_20191 = env  in
      {
        solver = (uu___261_20191.solver);
        range = (uu___261_20191.range);
        curmodule = (uu___261_20191.curmodule);
        gamma = (uu___261_20191.gamma);
        gamma_sig = (uu___261_20191.gamma_sig);
        gamma_cache = (uu___261_20191.gamma_cache);
        modules = (uu___261_20191.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___261_20191.sigtab);
        attrtab = (uu___261_20191.attrtab);
        is_pattern = (uu___261_20191.is_pattern);
        instantiate_imp = (uu___261_20191.instantiate_imp);
        effects = (uu___261_20191.effects);
        generalize = (uu___261_20191.generalize);
        letrecs = (uu___261_20191.letrecs);
        top_level = (uu___261_20191.top_level);
        check_uvars = (uu___261_20191.check_uvars);
        use_eq = false;
        is_iface = (uu___261_20191.is_iface);
        admit = (uu___261_20191.admit);
        lax = (uu___261_20191.lax);
        lax_universes = (uu___261_20191.lax_universes);
        phase1 = (uu___261_20191.phase1);
        failhard = (uu___261_20191.failhard);
        nosynth = (uu___261_20191.nosynth);
        uvar_subtyping = (uu___261_20191.uvar_subtyping);
        tc_term = (uu___261_20191.tc_term);
        type_of = (uu___261_20191.type_of);
        universe_of = (uu___261_20191.universe_of);
        check_type_of = (uu___261_20191.check_type_of);
        use_bv_sorts = (uu___261_20191.use_bv_sorts);
        qtbl_name_and_index = (uu___261_20191.qtbl_name_and_index);
        normalized_eff_names = (uu___261_20191.normalized_eff_names);
        fv_delta_depths = (uu___261_20191.fv_delta_depths);
        proof_ns = (uu___261_20191.proof_ns);
        synth_hook = (uu___261_20191.synth_hook);
        splice = (uu___261_20191.splice);
        is_native_tactic = (uu___261_20191.is_native_tactic);
        identifier_info = (uu___261_20191.identifier_info);
        tc_hooks = (uu___261_20191.tc_hooks);
        dsenv = (uu___261_20191.dsenv);
        nbe = (uu___261_20191.nbe)
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
    let uu____20219 = expected_typ env_  in
    ((let uu___262_20225 = env_  in
      {
        solver = (uu___262_20225.solver);
        range = (uu___262_20225.range);
        curmodule = (uu___262_20225.curmodule);
        gamma = (uu___262_20225.gamma);
        gamma_sig = (uu___262_20225.gamma_sig);
        gamma_cache = (uu___262_20225.gamma_cache);
        modules = (uu___262_20225.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___262_20225.sigtab);
        attrtab = (uu___262_20225.attrtab);
        is_pattern = (uu___262_20225.is_pattern);
        instantiate_imp = (uu___262_20225.instantiate_imp);
        effects = (uu___262_20225.effects);
        generalize = (uu___262_20225.generalize);
        letrecs = (uu___262_20225.letrecs);
        top_level = (uu___262_20225.top_level);
        check_uvars = (uu___262_20225.check_uvars);
        use_eq = false;
        is_iface = (uu___262_20225.is_iface);
        admit = (uu___262_20225.admit);
        lax = (uu___262_20225.lax);
        lax_universes = (uu___262_20225.lax_universes);
        phase1 = (uu___262_20225.phase1);
        failhard = (uu___262_20225.failhard);
        nosynth = (uu___262_20225.nosynth);
        uvar_subtyping = (uu___262_20225.uvar_subtyping);
        tc_term = (uu___262_20225.tc_term);
        type_of = (uu___262_20225.type_of);
        universe_of = (uu___262_20225.universe_of);
        check_type_of = (uu___262_20225.check_type_of);
        use_bv_sorts = (uu___262_20225.use_bv_sorts);
        qtbl_name_and_index = (uu___262_20225.qtbl_name_and_index);
        normalized_eff_names = (uu___262_20225.normalized_eff_names);
        fv_delta_depths = (uu___262_20225.fv_delta_depths);
        proof_ns = (uu___262_20225.proof_ns);
        synth_hook = (uu___262_20225.synth_hook);
        splice = (uu___262_20225.splice);
        is_native_tactic = (uu___262_20225.is_native_tactic);
        identifier_info = (uu___262_20225.identifier_info);
        tc_hooks = (uu___262_20225.tc_hooks);
        dsenv = (uu___262_20225.dsenv);
        nbe = (uu___262_20225.nbe)
      }), uu____20219)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____20235 =
      let uu____20238 = FStar_Ident.id_of_text ""  in [uu____20238]  in
    FStar_Ident.lid_of_ids uu____20235  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____20244 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____20244
        then
          let uu____20247 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____20247 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___263_20274 = env  in
       {
         solver = (uu___263_20274.solver);
         range = (uu___263_20274.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___263_20274.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___263_20274.expected_typ);
         sigtab = (uu___263_20274.sigtab);
         attrtab = (uu___263_20274.attrtab);
         is_pattern = (uu___263_20274.is_pattern);
         instantiate_imp = (uu___263_20274.instantiate_imp);
         effects = (uu___263_20274.effects);
         generalize = (uu___263_20274.generalize);
         letrecs = (uu___263_20274.letrecs);
         top_level = (uu___263_20274.top_level);
         check_uvars = (uu___263_20274.check_uvars);
         use_eq = (uu___263_20274.use_eq);
         is_iface = (uu___263_20274.is_iface);
         admit = (uu___263_20274.admit);
         lax = (uu___263_20274.lax);
         lax_universes = (uu___263_20274.lax_universes);
         phase1 = (uu___263_20274.phase1);
         failhard = (uu___263_20274.failhard);
         nosynth = (uu___263_20274.nosynth);
         uvar_subtyping = (uu___263_20274.uvar_subtyping);
         tc_term = (uu___263_20274.tc_term);
         type_of = (uu___263_20274.type_of);
         universe_of = (uu___263_20274.universe_of);
         check_type_of = (uu___263_20274.check_type_of);
         use_bv_sorts = (uu___263_20274.use_bv_sorts);
         qtbl_name_and_index = (uu___263_20274.qtbl_name_and_index);
         normalized_eff_names = (uu___263_20274.normalized_eff_names);
         fv_delta_depths = (uu___263_20274.fv_delta_depths);
         proof_ns = (uu___263_20274.proof_ns);
         synth_hook = (uu___263_20274.synth_hook);
         splice = (uu___263_20274.splice);
         is_native_tactic = (uu___263_20274.is_native_tactic);
         identifier_info = (uu___263_20274.identifier_info);
         tc_hooks = (uu___263_20274.tc_hooks);
         dsenv = (uu___263_20274.dsenv);
         nbe = (uu___263_20274.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20325)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20329,(uu____20330,t)))::tl1
          ->
          let uu____20351 =
            let uu____20354 = FStar_Syntax_Free.uvars t  in
            ext out uu____20354  in
          aux uu____20351 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20357;
            FStar_Syntax_Syntax.index = uu____20358;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20365 =
            let uu____20368 = FStar_Syntax_Free.uvars t  in
            ext out uu____20368  in
          aux uu____20365 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20425)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20429,(uu____20430,t)))::tl1
          ->
          let uu____20451 =
            let uu____20454 = FStar_Syntax_Free.univs t  in
            ext out uu____20454  in
          aux uu____20451 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20457;
            FStar_Syntax_Syntax.index = uu____20458;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20465 =
            let uu____20468 = FStar_Syntax_Free.univs t  in
            ext out uu____20468  in
          aux uu____20465 tl1
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
          let uu____20529 = FStar_Util.set_add uname out  in
          aux uu____20529 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20532,(uu____20533,t)))::tl1
          ->
          let uu____20554 =
            let uu____20557 = FStar_Syntax_Free.univnames t  in
            ext out uu____20557  in
          aux uu____20554 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20560;
            FStar_Syntax_Syntax.index = uu____20561;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20568 =
            let uu____20571 = FStar_Syntax_Free.univnames t  in
            ext out uu____20571  in
          aux uu____20568 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___237_20591  ->
            match uu___237_20591 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20595 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20608 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20618 =
      let uu____20627 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20627
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20618 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20671 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___238_20681  ->
              match uu___238_20681 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20683 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20683
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20686) ->
                  let uu____20703 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20703))
       in
    FStar_All.pipe_right uu____20671 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___239_20710  ->
    match uu___239_20710 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20712 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20712
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20732  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20774) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20793,uu____20794) -> false  in
      let uu____20803 =
        FStar_List.tryFind
          (fun uu____20821  ->
             match uu____20821 with | (p,uu____20829) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20803 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20840,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20862 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20862
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___264_20880 = e  in
        {
          solver = (uu___264_20880.solver);
          range = (uu___264_20880.range);
          curmodule = (uu___264_20880.curmodule);
          gamma = (uu___264_20880.gamma);
          gamma_sig = (uu___264_20880.gamma_sig);
          gamma_cache = (uu___264_20880.gamma_cache);
          modules = (uu___264_20880.modules);
          expected_typ = (uu___264_20880.expected_typ);
          sigtab = (uu___264_20880.sigtab);
          attrtab = (uu___264_20880.attrtab);
          is_pattern = (uu___264_20880.is_pattern);
          instantiate_imp = (uu___264_20880.instantiate_imp);
          effects = (uu___264_20880.effects);
          generalize = (uu___264_20880.generalize);
          letrecs = (uu___264_20880.letrecs);
          top_level = (uu___264_20880.top_level);
          check_uvars = (uu___264_20880.check_uvars);
          use_eq = (uu___264_20880.use_eq);
          is_iface = (uu___264_20880.is_iface);
          admit = (uu___264_20880.admit);
          lax = (uu___264_20880.lax);
          lax_universes = (uu___264_20880.lax_universes);
          phase1 = (uu___264_20880.phase1);
          failhard = (uu___264_20880.failhard);
          nosynth = (uu___264_20880.nosynth);
          uvar_subtyping = (uu___264_20880.uvar_subtyping);
          tc_term = (uu___264_20880.tc_term);
          type_of = (uu___264_20880.type_of);
          universe_of = (uu___264_20880.universe_of);
          check_type_of = (uu___264_20880.check_type_of);
          use_bv_sorts = (uu___264_20880.use_bv_sorts);
          qtbl_name_and_index = (uu___264_20880.qtbl_name_and_index);
          normalized_eff_names = (uu___264_20880.normalized_eff_names);
          fv_delta_depths = (uu___264_20880.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___264_20880.synth_hook);
          splice = (uu___264_20880.splice);
          is_native_tactic = (uu___264_20880.is_native_tactic);
          identifier_info = (uu___264_20880.identifier_info);
          tc_hooks = (uu___264_20880.tc_hooks);
          dsenv = (uu___264_20880.dsenv);
          nbe = (uu___264_20880.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___265_20920 = e  in
      {
        solver = (uu___265_20920.solver);
        range = (uu___265_20920.range);
        curmodule = (uu___265_20920.curmodule);
        gamma = (uu___265_20920.gamma);
        gamma_sig = (uu___265_20920.gamma_sig);
        gamma_cache = (uu___265_20920.gamma_cache);
        modules = (uu___265_20920.modules);
        expected_typ = (uu___265_20920.expected_typ);
        sigtab = (uu___265_20920.sigtab);
        attrtab = (uu___265_20920.attrtab);
        is_pattern = (uu___265_20920.is_pattern);
        instantiate_imp = (uu___265_20920.instantiate_imp);
        effects = (uu___265_20920.effects);
        generalize = (uu___265_20920.generalize);
        letrecs = (uu___265_20920.letrecs);
        top_level = (uu___265_20920.top_level);
        check_uvars = (uu___265_20920.check_uvars);
        use_eq = (uu___265_20920.use_eq);
        is_iface = (uu___265_20920.is_iface);
        admit = (uu___265_20920.admit);
        lax = (uu___265_20920.lax);
        lax_universes = (uu___265_20920.lax_universes);
        phase1 = (uu___265_20920.phase1);
        failhard = (uu___265_20920.failhard);
        nosynth = (uu___265_20920.nosynth);
        uvar_subtyping = (uu___265_20920.uvar_subtyping);
        tc_term = (uu___265_20920.tc_term);
        type_of = (uu___265_20920.type_of);
        universe_of = (uu___265_20920.universe_of);
        check_type_of = (uu___265_20920.check_type_of);
        use_bv_sorts = (uu___265_20920.use_bv_sorts);
        qtbl_name_and_index = (uu___265_20920.qtbl_name_and_index);
        normalized_eff_names = (uu___265_20920.normalized_eff_names);
        fv_delta_depths = (uu___265_20920.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___265_20920.synth_hook);
        splice = (uu___265_20920.splice);
        is_native_tactic = (uu___265_20920.is_native_tactic);
        identifier_info = (uu___265_20920.identifier_info);
        tc_hooks = (uu___265_20920.tc_hooks);
        dsenv = (uu___265_20920.dsenv);
        nbe = (uu___265_20920.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20935 = FStar_Syntax_Free.names t  in
      let uu____20938 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20935 uu____20938
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20959 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20959
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20967 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20967
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20984 =
      match uu____20984 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20994 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20994)
       in
    let uu____20996 =
      let uu____20999 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20999 FStar_List.rev  in
    FStar_All.pipe_right uu____20996 (FStar_String.concat " ")
  
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
                  (let uu____21052 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____21052 with
                   | FStar_Pervasives_Native.Some uu____21055 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____21056 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____21062;
        univ_ineqs = uu____21063; implicits = uu____21064;_} -> true
    | uu____21075 -> false
  
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
          let uu___266_21102 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___266_21102.deferred);
            univ_ineqs = (uu___266_21102.univ_ineqs);
            implicits = (uu___266_21102.implicits)
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
          let uu____21137 = FStar_Options.defensive ()  in
          if uu____21137
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____21141 =
              let uu____21142 =
                let uu____21143 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____21143  in
              Prims.op_Negation uu____21142  in
            (if uu____21141
             then
               let uu____21148 =
                 let uu____21153 =
                   let uu____21154 = FStar_Syntax_Print.term_to_string t  in
                   let uu____21155 =
                     let uu____21156 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____21156
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____21154 uu____21155
                    in
                 (FStar_Errors.Warning_Defensive, uu____21153)  in
               FStar_Errors.log_issue rng uu____21148
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
          let uu____21187 =
            let uu____21188 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____21188  in
          if uu____21187
          then ()
          else
            (let uu____21190 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____21190 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____21213 =
            let uu____21214 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____21214  in
          if uu____21213
          then ()
          else
            (let uu____21216 = bound_vars e  in
             def_check_closed_in rng msg uu____21216 t)
  
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
          let uu___267_21251 = g  in
          let uu____21252 =
            let uu____21253 =
              let uu____21254 =
                let uu____21261 =
                  let uu____21262 =
                    let uu____21279 =
                      let uu____21290 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____21290]  in
                    (f, uu____21279)  in
                  FStar_Syntax_Syntax.Tm_app uu____21262  in
                FStar_Syntax_Syntax.mk uu____21261  in
              uu____21254 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____21253
             in
          {
            guard_f = uu____21252;
            deferred = (uu___267_21251.deferred);
            univ_ineqs = (uu___267_21251.univ_ineqs);
            implicits = (uu___267_21251.implicits)
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
          let uu___268_21346 = g  in
          let uu____21347 =
            let uu____21348 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____21348  in
          {
            guard_f = uu____21347;
            deferred = (uu___268_21346.deferred);
            univ_ineqs = (uu___268_21346.univ_ineqs);
            implicits = (uu___268_21346.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___269_21364 = g  in
          let uu____21365 =
            let uu____21366 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____21366  in
          {
            guard_f = uu____21365;
            deferred = (uu___269_21364.deferred);
            univ_ineqs = (uu___269_21364.univ_ineqs);
            implicits = (uu___269_21364.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___270_21368 = g  in
          let uu____21369 =
            let uu____21370 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____21370  in
          {
            guard_f = uu____21369;
            deferred = (uu___270_21368.deferred);
            univ_ineqs = (uu___270_21368.univ_ineqs);
            implicits = (uu___270_21368.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____21376 ->
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
          let uu____21391 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____21391
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____21397 =
      let uu____21398 = FStar_Syntax_Util.unmeta t  in
      uu____21398.FStar_Syntax_Syntax.n  in
    match uu____21397 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21402 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____21443 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____21443;
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
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_List.fold_left conj_guard trivial_guard gs 
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
                       let uu____21533 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21533
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___271_21537 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___271_21537.deferred);
              univ_ineqs = (uu___271_21537.univ_ineqs);
              implicits = (uu___271_21537.implicits)
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
               let uu____21570 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21570
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
            let uu___272_21593 = g  in
            let uu____21594 =
              let uu____21595 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21595  in
            {
              guard_f = uu____21594;
              deferred = (uu___272_21593.deferred);
              univ_ineqs = (uu___272_21593.univ_ineqs);
              implicits = (uu___272_21593.implicits)
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
            let uu____21633 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21633 with
            | FStar_Pervasives_Native.Some
                (uu____21658::(tm,uu____21660)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21724 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21742 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21742;
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
                    let uu___273_21777 = trivial_guard  in
                    {
                      guard_f = (uu___273_21777.guard_f);
                      deferred = (uu___273_21777.deferred);
                      univ_ineqs = (uu___273_21777.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21794  -> ());
    push = (fun uu____21796  -> ());
    pop = (fun uu____21798  -> ());
    snapshot =
      (fun uu____21800  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21809  -> fun uu____21810  -> ());
    encode_modul = (fun uu____21821  -> fun uu____21822  -> ());
    encode_sig = (fun uu____21825  -> fun uu____21826  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21832 =
             let uu____21839 = FStar_Options.peek ()  in (e, g, uu____21839)
              in
           [uu____21832]);
    solve = (fun uu____21855  -> fun uu____21856  -> fun uu____21857  -> ());
    finish = (fun uu____21863  -> ());
    refresh = (fun uu____21865  -> ())
  } 