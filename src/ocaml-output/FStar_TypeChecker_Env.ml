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
  postprocess:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__splice
  
let (__proj__Mkenv__item__postprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
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
        splice = __fname__splice; postprocess = __fname__postprocess;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__postprocess
  
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
        splice = __fname__splice; postprocess = __fname__postprocess;
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
let (postprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  -> fun tau  -> fun ty  -> fun tm  -> env.postprocess env tau ty tm 
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___229_10749  ->
              match uu___229_10749 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____10752 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____10752  in
                  let uu____10753 =
                    let uu____10754 = FStar_Syntax_Subst.compress y  in
                    uu____10754.FStar_Syntax_Syntax.n  in
                  (match uu____10753 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____10758 =
                         let uu___243_10759 = y1  in
                         let uu____10760 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___243_10759.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___243_10759.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____10760
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____10758
                   | uu____10763 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___244_10775 = env  in
      let uu____10776 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___244_10775.solver);
        range = (uu___244_10775.range);
        curmodule = (uu___244_10775.curmodule);
        gamma = uu____10776;
        gamma_sig = (uu___244_10775.gamma_sig);
        gamma_cache = (uu___244_10775.gamma_cache);
        modules = (uu___244_10775.modules);
        expected_typ = (uu___244_10775.expected_typ);
        sigtab = (uu___244_10775.sigtab);
        attrtab = (uu___244_10775.attrtab);
        is_pattern = (uu___244_10775.is_pattern);
        instantiate_imp = (uu___244_10775.instantiate_imp);
        effects = (uu___244_10775.effects);
        generalize = (uu___244_10775.generalize);
        letrecs = (uu___244_10775.letrecs);
        top_level = (uu___244_10775.top_level);
        check_uvars = (uu___244_10775.check_uvars);
        use_eq = (uu___244_10775.use_eq);
        is_iface = (uu___244_10775.is_iface);
        admit = (uu___244_10775.admit);
        lax = (uu___244_10775.lax);
        lax_universes = (uu___244_10775.lax_universes);
        phase1 = (uu___244_10775.phase1);
        failhard = (uu___244_10775.failhard);
        nosynth = (uu___244_10775.nosynth);
        uvar_subtyping = (uu___244_10775.uvar_subtyping);
        tc_term = (uu___244_10775.tc_term);
        type_of = (uu___244_10775.type_of);
        universe_of = (uu___244_10775.universe_of);
        check_type_of = (uu___244_10775.check_type_of);
        use_bv_sorts = (uu___244_10775.use_bv_sorts);
        qtbl_name_and_index = (uu___244_10775.qtbl_name_and_index);
        normalized_eff_names = (uu___244_10775.normalized_eff_names);
        fv_delta_depths = (uu___244_10775.fv_delta_depths);
        proof_ns = (uu___244_10775.proof_ns);
        synth_hook = (uu___244_10775.synth_hook);
        splice = (uu___244_10775.splice);
        postprocess = (uu___244_10775.postprocess);
        is_native_tactic = (uu___244_10775.is_native_tactic);
        identifier_info = (uu___244_10775.identifier_info);
        tc_hooks = (uu___244_10775.tc_hooks);
        dsenv = (uu___244_10775.dsenv);
        nbe = (uu___244_10775.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____10783  -> fun uu____10784  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___245_10804 = env  in
      {
        solver = (uu___245_10804.solver);
        range = (uu___245_10804.range);
        curmodule = (uu___245_10804.curmodule);
        gamma = (uu___245_10804.gamma);
        gamma_sig = (uu___245_10804.gamma_sig);
        gamma_cache = (uu___245_10804.gamma_cache);
        modules = (uu___245_10804.modules);
        expected_typ = (uu___245_10804.expected_typ);
        sigtab = (uu___245_10804.sigtab);
        attrtab = (uu___245_10804.attrtab);
        is_pattern = (uu___245_10804.is_pattern);
        instantiate_imp = (uu___245_10804.instantiate_imp);
        effects = (uu___245_10804.effects);
        generalize = (uu___245_10804.generalize);
        letrecs = (uu___245_10804.letrecs);
        top_level = (uu___245_10804.top_level);
        check_uvars = (uu___245_10804.check_uvars);
        use_eq = (uu___245_10804.use_eq);
        is_iface = (uu___245_10804.is_iface);
        admit = (uu___245_10804.admit);
        lax = (uu___245_10804.lax);
        lax_universes = (uu___245_10804.lax_universes);
        phase1 = (uu___245_10804.phase1);
        failhard = (uu___245_10804.failhard);
        nosynth = (uu___245_10804.nosynth);
        uvar_subtyping = (uu___245_10804.uvar_subtyping);
        tc_term = (uu___245_10804.tc_term);
        type_of = (uu___245_10804.type_of);
        universe_of = (uu___245_10804.universe_of);
        check_type_of = (uu___245_10804.check_type_of);
        use_bv_sorts = (uu___245_10804.use_bv_sorts);
        qtbl_name_and_index = (uu___245_10804.qtbl_name_and_index);
        normalized_eff_names = (uu___245_10804.normalized_eff_names);
        fv_delta_depths = (uu___245_10804.fv_delta_depths);
        proof_ns = (uu___245_10804.proof_ns);
        synth_hook = (uu___245_10804.synth_hook);
        splice = (uu___245_10804.splice);
        postprocess = (uu___245_10804.postprocess);
        is_native_tactic = (uu___245_10804.is_native_tactic);
        identifier_info = (uu___245_10804.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___245_10804.dsenv);
        nbe = (uu___245_10804.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___246_10815 = e  in
      let uu____10816 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___246_10815.solver);
        range = (uu___246_10815.range);
        curmodule = (uu___246_10815.curmodule);
        gamma = (uu___246_10815.gamma);
        gamma_sig = (uu___246_10815.gamma_sig);
        gamma_cache = (uu___246_10815.gamma_cache);
        modules = (uu___246_10815.modules);
        expected_typ = (uu___246_10815.expected_typ);
        sigtab = (uu___246_10815.sigtab);
        attrtab = (uu___246_10815.attrtab);
        is_pattern = (uu___246_10815.is_pattern);
        instantiate_imp = (uu___246_10815.instantiate_imp);
        effects = (uu___246_10815.effects);
        generalize = (uu___246_10815.generalize);
        letrecs = (uu___246_10815.letrecs);
        top_level = (uu___246_10815.top_level);
        check_uvars = (uu___246_10815.check_uvars);
        use_eq = (uu___246_10815.use_eq);
        is_iface = (uu___246_10815.is_iface);
        admit = (uu___246_10815.admit);
        lax = (uu___246_10815.lax);
        lax_universes = (uu___246_10815.lax_universes);
        phase1 = (uu___246_10815.phase1);
        failhard = (uu___246_10815.failhard);
        nosynth = (uu___246_10815.nosynth);
        uvar_subtyping = (uu___246_10815.uvar_subtyping);
        tc_term = (uu___246_10815.tc_term);
        type_of = (uu___246_10815.type_of);
        universe_of = (uu___246_10815.universe_of);
        check_type_of = (uu___246_10815.check_type_of);
        use_bv_sorts = (uu___246_10815.use_bv_sorts);
        qtbl_name_and_index = (uu___246_10815.qtbl_name_and_index);
        normalized_eff_names = (uu___246_10815.normalized_eff_names);
        fv_delta_depths = (uu___246_10815.fv_delta_depths);
        proof_ns = (uu___246_10815.proof_ns);
        synth_hook = (uu___246_10815.synth_hook);
        splice = (uu___246_10815.splice);
        postprocess = (uu___246_10815.postprocess);
        is_native_tactic = (uu___246_10815.is_native_tactic);
        identifier_info = (uu___246_10815.identifier_info);
        tc_hooks = (uu___246_10815.tc_hooks);
        dsenv = uu____10816;
        nbe = (uu___246_10815.nbe)
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
      | (NoDelta ,uu____10839) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____10840,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____10841,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____10842 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____10851 . unit -> 'Auu____10851 FStar_Util.smap =
  fun uu____10858  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____10863 . unit -> 'Auu____10863 FStar_Util.smap =
  fun uu____10870  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____11004 = new_gamma_cache ()  in
                  let uu____11007 = new_sigtab ()  in
                  let uu____11010 = new_sigtab ()  in
                  let uu____11017 =
                    let uu____11030 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____11030, FStar_Pervasives_Native.None)  in
                  let uu____11045 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____11048 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____11051 = FStar_Options.using_facts_from ()  in
                  let uu____11052 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____11055 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____11004;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____11007;
                    attrtab = uu____11010;
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
                    qtbl_name_and_index = uu____11017;
                    normalized_eff_names = uu____11045;
                    fv_delta_depths = uu____11048;
                    proof_ns = uu____11051;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____11099  -> false);
                    identifier_info = uu____11052;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____11055;
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
  fun uu____11199  ->
    let uu____11200 = FStar_ST.op_Bang query_indices  in
    match uu____11200 with
    | [] -> failwith "Empty query indices!"
    | uu____11250 ->
        let uu____11259 =
          let uu____11268 =
            let uu____11275 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____11275  in
          let uu____11325 = FStar_ST.op_Bang query_indices  in uu____11268 ::
            uu____11325
           in
        FStar_ST.op_Colon_Equals query_indices uu____11259
  
let (pop_query_indices : unit -> unit) =
  fun uu____11414  ->
    let uu____11415 = FStar_ST.op_Bang query_indices  in
    match uu____11415 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____11530  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____11560  ->
    match uu____11560 with
    | (l,n1) ->
        let uu____11567 = FStar_ST.op_Bang query_indices  in
        (match uu____11567 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____11678 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____11697  ->
    let uu____11698 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____11698
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____11771 =
       let uu____11774 = FStar_ST.op_Bang stack  in env :: uu____11774  in
     FStar_ST.op_Colon_Equals stack uu____11771);
    (let uu___247_11823 = env  in
     let uu____11824 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____11827 = FStar_Util.smap_copy (sigtab env)  in
     let uu____11830 = FStar_Util.smap_copy (attrtab env)  in
     let uu____11837 =
       let uu____11850 =
         let uu____11853 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____11853  in
       let uu____11878 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____11850, uu____11878)  in
     let uu____11919 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____11922 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____11925 =
       let uu____11928 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____11928  in
     {
       solver = (uu___247_11823.solver);
       range = (uu___247_11823.range);
       curmodule = (uu___247_11823.curmodule);
       gamma = (uu___247_11823.gamma);
       gamma_sig = (uu___247_11823.gamma_sig);
       gamma_cache = uu____11824;
       modules = (uu___247_11823.modules);
       expected_typ = (uu___247_11823.expected_typ);
       sigtab = uu____11827;
       attrtab = uu____11830;
       is_pattern = (uu___247_11823.is_pattern);
       instantiate_imp = (uu___247_11823.instantiate_imp);
       effects = (uu___247_11823.effects);
       generalize = (uu___247_11823.generalize);
       letrecs = (uu___247_11823.letrecs);
       top_level = (uu___247_11823.top_level);
       check_uvars = (uu___247_11823.check_uvars);
       use_eq = (uu___247_11823.use_eq);
       is_iface = (uu___247_11823.is_iface);
       admit = (uu___247_11823.admit);
       lax = (uu___247_11823.lax);
       lax_universes = (uu___247_11823.lax_universes);
       phase1 = (uu___247_11823.phase1);
       failhard = (uu___247_11823.failhard);
       nosynth = (uu___247_11823.nosynth);
       uvar_subtyping = (uu___247_11823.uvar_subtyping);
       tc_term = (uu___247_11823.tc_term);
       type_of = (uu___247_11823.type_of);
       universe_of = (uu___247_11823.universe_of);
       check_type_of = (uu___247_11823.check_type_of);
       use_bv_sorts = (uu___247_11823.use_bv_sorts);
       qtbl_name_and_index = uu____11837;
       normalized_eff_names = uu____11919;
       fv_delta_depths = uu____11922;
       proof_ns = (uu___247_11823.proof_ns);
       synth_hook = (uu___247_11823.synth_hook);
       splice = (uu___247_11823.splice);
       postprocess = (uu___247_11823.postprocess);
       is_native_tactic = (uu___247_11823.is_native_tactic);
       identifier_info = uu____11925;
       tc_hooks = (uu___247_11823.tc_hooks);
       dsenv = (uu___247_11823.dsenv);
       nbe = (uu___247_11823.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11974  ->
    let uu____11975 = FStar_ST.op_Bang stack  in
    match uu____11975 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____12029 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____12101  ->
           let uu____12102 = snapshot_stack env  in
           match uu____12102 with
           | (stack_depth,env1) ->
               let uu____12127 = snapshot_query_indices ()  in
               (match uu____12127 with
                | (query_indices_depth,()) ->
                    let uu____12151 = (env1.solver).snapshot msg  in
                    (match uu____12151 with
                     | (solver_depth,()) ->
                         let uu____12193 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____12193 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___248_12239 = env1  in
                                 {
                                   solver = (uu___248_12239.solver);
                                   range = (uu___248_12239.range);
                                   curmodule = (uu___248_12239.curmodule);
                                   gamma = (uu___248_12239.gamma);
                                   gamma_sig = (uu___248_12239.gamma_sig);
                                   gamma_cache = (uu___248_12239.gamma_cache);
                                   modules = (uu___248_12239.modules);
                                   expected_typ =
                                     (uu___248_12239.expected_typ);
                                   sigtab = (uu___248_12239.sigtab);
                                   attrtab = (uu___248_12239.attrtab);
                                   is_pattern = (uu___248_12239.is_pattern);
                                   instantiate_imp =
                                     (uu___248_12239.instantiate_imp);
                                   effects = (uu___248_12239.effects);
                                   generalize = (uu___248_12239.generalize);
                                   letrecs = (uu___248_12239.letrecs);
                                   top_level = (uu___248_12239.top_level);
                                   check_uvars = (uu___248_12239.check_uvars);
                                   use_eq = (uu___248_12239.use_eq);
                                   is_iface = (uu___248_12239.is_iface);
                                   admit = (uu___248_12239.admit);
                                   lax = (uu___248_12239.lax);
                                   lax_universes =
                                     (uu___248_12239.lax_universes);
                                   phase1 = (uu___248_12239.phase1);
                                   failhard = (uu___248_12239.failhard);
                                   nosynth = (uu___248_12239.nosynth);
                                   uvar_subtyping =
                                     (uu___248_12239.uvar_subtyping);
                                   tc_term = (uu___248_12239.tc_term);
                                   type_of = (uu___248_12239.type_of);
                                   universe_of = (uu___248_12239.universe_of);
                                   check_type_of =
                                     (uu___248_12239.check_type_of);
                                   use_bv_sorts =
                                     (uu___248_12239.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___248_12239.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___248_12239.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___248_12239.fv_delta_depths);
                                   proof_ns = (uu___248_12239.proof_ns);
                                   synth_hook = (uu___248_12239.synth_hook);
                                   splice = (uu___248_12239.splice);
                                   postprocess = (uu___248_12239.postprocess);
                                   is_native_tactic =
                                     (uu___248_12239.is_native_tactic);
                                   identifier_info =
                                     (uu___248_12239.identifier_info);
                                   tc_hooks = (uu___248_12239.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___248_12239.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____12270  ->
             let uu____12271 =
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
             match uu____12271 with
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
                             ((let uu____12397 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____12397
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____12408 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____12408
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____12435,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____12467 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____12493  ->
                  match uu____12493 with
                  | (m,uu____12499) -> FStar_Ident.lid_equals l m))
           in
        (match uu____12467 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___249_12507 = env  in
               {
                 solver = (uu___249_12507.solver);
                 range = (uu___249_12507.range);
                 curmodule = (uu___249_12507.curmodule);
                 gamma = (uu___249_12507.gamma);
                 gamma_sig = (uu___249_12507.gamma_sig);
                 gamma_cache = (uu___249_12507.gamma_cache);
                 modules = (uu___249_12507.modules);
                 expected_typ = (uu___249_12507.expected_typ);
                 sigtab = (uu___249_12507.sigtab);
                 attrtab = (uu___249_12507.attrtab);
                 is_pattern = (uu___249_12507.is_pattern);
                 instantiate_imp = (uu___249_12507.instantiate_imp);
                 effects = (uu___249_12507.effects);
                 generalize = (uu___249_12507.generalize);
                 letrecs = (uu___249_12507.letrecs);
                 top_level = (uu___249_12507.top_level);
                 check_uvars = (uu___249_12507.check_uvars);
                 use_eq = (uu___249_12507.use_eq);
                 is_iface = (uu___249_12507.is_iface);
                 admit = (uu___249_12507.admit);
                 lax = (uu___249_12507.lax);
                 lax_universes = (uu___249_12507.lax_universes);
                 phase1 = (uu___249_12507.phase1);
                 failhard = (uu___249_12507.failhard);
                 nosynth = (uu___249_12507.nosynth);
                 uvar_subtyping = (uu___249_12507.uvar_subtyping);
                 tc_term = (uu___249_12507.tc_term);
                 type_of = (uu___249_12507.type_of);
                 universe_of = (uu___249_12507.universe_of);
                 check_type_of = (uu___249_12507.check_type_of);
                 use_bv_sorts = (uu___249_12507.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___249_12507.normalized_eff_names);
                 fv_delta_depths = (uu___249_12507.fv_delta_depths);
                 proof_ns = (uu___249_12507.proof_ns);
                 synth_hook = (uu___249_12507.synth_hook);
                 splice = (uu___249_12507.splice);
                 postprocess = (uu___249_12507.postprocess);
                 is_native_tactic = (uu___249_12507.is_native_tactic);
                 identifier_info = (uu___249_12507.identifier_info);
                 tc_hooks = (uu___249_12507.tc_hooks);
                 dsenv = (uu___249_12507.dsenv);
                 nbe = (uu___249_12507.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____12520,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___250_12529 = env  in
               {
                 solver = (uu___250_12529.solver);
                 range = (uu___250_12529.range);
                 curmodule = (uu___250_12529.curmodule);
                 gamma = (uu___250_12529.gamma);
                 gamma_sig = (uu___250_12529.gamma_sig);
                 gamma_cache = (uu___250_12529.gamma_cache);
                 modules = (uu___250_12529.modules);
                 expected_typ = (uu___250_12529.expected_typ);
                 sigtab = (uu___250_12529.sigtab);
                 attrtab = (uu___250_12529.attrtab);
                 is_pattern = (uu___250_12529.is_pattern);
                 instantiate_imp = (uu___250_12529.instantiate_imp);
                 effects = (uu___250_12529.effects);
                 generalize = (uu___250_12529.generalize);
                 letrecs = (uu___250_12529.letrecs);
                 top_level = (uu___250_12529.top_level);
                 check_uvars = (uu___250_12529.check_uvars);
                 use_eq = (uu___250_12529.use_eq);
                 is_iface = (uu___250_12529.is_iface);
                 admit = (uu___250_12529.admit);
                 lax = (uu___250_12529.lax);
                 lax_universes = (uu___250_12529.lax_universes);
                 phase1 = (uu___250_12529.phase1);
                 failhard = (uu___250_12529.failhard);
                 nosynth = (uu___250_12529.nosynth);
                 uvar_subtyping = (uu___250_12529.uvar_subtyping);
                 tc_term = (uu___250_12529.tc_term);
                 type_of = (uu___250_12529.type_of);
                 universe_of = (uu___250_12529.universe_of);
                 check_type_of = (uu___250_12529.check_type_of);
                 use_bv_sorts = (uu___250_12529.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___250_12529.normalized_eff_names);
                 fv_delta_depths = (uu___250_12529.fv_delta_depths);
                 proof_ns = (uu___250_12529.proof_ns);
                 synth_hook = (uu___250_12529.synth_hook);
                 splice = (uu___250_12529.splice);
                 postprocess = (uu___250_12529.postprocess);
                 is_native_tactic = (uu___250_12529.is_native_tactic);
                 identifier_info = (uu___250_12529.identifier_info);
                 tc_hooks = (uu___250_12529.tc_hooks);
                 dsenv = (uu___250_12529.dsenv);
                 nbe = (uu___250_12529.nbe)
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
        (let uu___251_12563 = e  in
         {
           solver = (uu___251_12563.solver);
           range = r;
           curmodule = (uu___251_12563.curmodule);
           gamma = (uu___251_12563.gamma);
           gamma_sig = (uu___251_12563.gamma_sig);
           gamma_cache = (uu___251_12563.gamma_cache);
           modules = (uu___251_12563.modules);
           expected_typ = (uu___251_12563.expected_typ);
           sigtab = (uu___251_12563.sigtab);
           attrtab = (uu___251_12563.attrtab);
           is_pattern = (uu___251_12563.is_pattern);
           instantiate_imp = (uu___251_12563.instantiate_imp);
           effects = (uu___251_12563.effects);
           generalize = (uu___251_12563.generalize);
           letrecs = (uu___251_12563.letrecs);
           top_level = (uu___251_12563.top_level);
           check_uvars = (uu___251_12563.check_uvars);
           use_eq = (uu___251_12563.use_eq);
           is_iface = (uu___251_12563.is_iface);
           admit = (uu___251_12563.admit);
           lax = (uu___251_12563.lax);
           lax_universes = (uu___251_12563.lax_universes);
           phase1 = (uu___251_12563.phase1);
           failhard = (uu___251_12563.failhard);
           nosynth = (uu___251_12563.nosynth);
           uvar_subtyping = (uu___251_12563.uvar_subtyping);
           tc_term = (uu___251_12563.tc_term);
           type_of = (uu___251_12563.type_of);
           universe_of = (uu___251_12563.universe_of);
           check_type_of = (uu___251_12563.check_type_of);
           use_bv_sorts = (uu___251_12563.use_bv_sorts);
           qtbl_name_and_index = (uu___251_12563.qtbl_name_and_index);
           normalized_eff_names = (uu___251_12563.normalized_eff_names);
           fv_delta_depths = (uu___251_12563.fv_delta_depths);
           proof_ns = (uu___251_12563.proof_ns);
           synth_hook = (uu___251_12563.synth_hook);
           splice = (uu___251_12563.splice);
           postprocess = (uu___251_12563.postprocess);
           is_native_tactic = (uu___251_12563.is_native_tactic);
           identifier_info = (uu___251_12563.identifier_info);
           tc_hooks = (uu___251_12563.tc_hooks);
           dsenv = (uu___251_12563.dsenv);
           nbe = (uu___251_12563.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____12579 =
        let uu____12580 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____12580 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____12579
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____12634 =
          let uu____12635 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____12635 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____12634
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____12689 =
          let uu____12690 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____12690 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____12689
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____12744 =
        let uu____12745 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____12745 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____12744
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___252_12806 = env  in
      {
        solver = (uu___252_12806.solver);
        range = (uu___252_12806.range);
        curmodule = lid;
        gamma = (uu___252_12806.gamma);
        gamma_sig = (uu___252_12806.gamma_sig);
        gamma_cache = (uu___252_12806.gamma_cache);
        modules = (uu___252_12806.modules);
        expected_typ = (uu___252_12806.expected_typ);
        sigtab = (uu___252_12806.sigtab);
        attrtab = (uu___252_12806.attrtab);
        is_pattern = (uu___252_12806.is_pattern);
        instantiate_imp = (uu___252_12806.instantiate_imp);
        effects = (uu___252_12806.effects);
        generalize = (uu___252_12806.generalize);
        letrecs = (uu___252_12806.letrecs);
        top_level = (uu___252_12806.top_level);
        check_uvars = (uu___252_12806.check_uvars);
        use_eq = (uu___252_12806.use_eq);
        is_iface = (uu___252_12806.is_iface);
        admit = (uu___252_12806.admit);
        lax = (uu___252_12806.lax);
        lax_universes = (uu___252_12806.lax_universes);
        phase1 = (uu___252_12806.phase1);
        failhard = (uu___252_12806.failhard);
        nosynth = (uu___252_12806.nosynth);
        uvar_subtyping = (uu___252_12806.uvar_subtyping);
        tc_term = (uu___252_12806.tc_term);
        type_of = (uu___252_12806.type_of);
        universe_of = (uu___252_12806.universe_of);
        check_type_of = (uu___252_12806.check_type_of);
        use_bv_sorts = (uu___252_12806.use_bv_sorts);
        qtbl_name_and_index = (uu___252_12806.qtbl_name_and_index);
        normalized_eff_names = (uu___252_12806.normalized_eff_names);
        fv_delta_depths = (uu___252_12806.fv_delta_depths);
        proof_ns = (uu___252_12806.proof_ns);
        synth_hook = (uu___252_12806.synth_hook);
        splice = (uu___252_12806.splice);
        postprocess = (uu___252_12806.postprocess);
        is_native_tactic = (uu___252_12806.is_native_tactic);
        identifier_info = (uu___252_12806.identifier_info);
        tc_hooks = (uu___252_12806.tc_hooks);
        dsenv = (uu___252_12806.dsenv);
        nbe = (uu___252_12806.nbe)
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
      let uu____12833 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____12833
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____12843 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____12843)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____12853 =
      let uu____12854 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____12854  in
    (FStar_Errors.Fatal_VariableNotFound, uu____12853)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____12859  ->
    let uu____12860 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____12860
  
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
      | ((formals,t),uu____12954) ->
          let vs = mk_univ_subst formals us  in
          let uu____12978 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12978)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___230_12994  ->
    match uu___230_12994 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____13020  -> new_u_univ ()))
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
      let uu____13039 = inst_tscheme t  in
      match uu____13039 with
      | (us,t1) ->
          let uu____13050 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____13050)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____13070  ->
          match uu____13070 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____13091 =
                         let uu____13092 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____13093 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____13094 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____13095 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____13092 uu____13093 uu____13094 uu____13095
                          in
                       failwith uu____13091)
                    else ();
                    (let uu____13097 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____13097))
               | uu____13106 ->
                   let uu____13107 =
                     let uu____13108 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____13108
                      in
                   failwith uu____13107)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____13114 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____13120 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____13126 -> false
  
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
             | ([],uu____13168) -> Maybe
             | (uu____13175,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____13194 -> No  in
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
          let uu____13285 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____13285 with
          | FStar_Pervasives_Native.None  ->
              let uu____13308 =
                FStar_Util.find_map env.gamma
                  (fun uu___231_13352  ->
                     match uu___231_13352 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____13391 = FStar_Ident.lid_equals lid l  in
                         if uu____13391
                         then
                           let uu____13412 =
                             let uu____13431 =
                               let uu____13446 = inst_tscheme t  in
                               FStar_Util.Inl uu____13446  in
                             let uu____13461 = FStar_Ident.range_of_lid l  in
                             (uu____13431, uu____13461)  in
                           FStar_Pervasives_Native.Some uu____13412
                         else FStar_Pervasives_Native.None
                     | uu____13513 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____13308
                (fun uu____13551  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___232_13560  ->
                        match uu___232_13560 with
                        | (uu____13563,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____13565);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____13566;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____13567;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____13568;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____13569;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____13589 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____13589
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
                                  uu____13637 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____13644 -> cache t  in
                            let uu____13645 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____13645 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____13651 =
                                   let uu____13652 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____13652)
                                    in
                                 maybe_cache uu____13651)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____13720 = find_in_sigtab env lid  in
         match uu____13720 with
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
      let uu____13800 = lookup_qname env lid  in
      match uu____13800 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____13821,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13932 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13932 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13974 =
          let uu____13977 = lookup_attr env1 attr  in se1 :: uu____13977  in
        FStar_Util.smap_add (attrtab env1) attr uu____13974  in
      FStar_List.iter
        (fun attr  ->
           let uu____13987 =
             let uu____13988 = FStar_Syntax_Subst.compress attr  in
             uu____13988.FStar_Syntax_Syntax.n  in
           match uu____13987 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13992 =
                 let uu____13993 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13993.FStar_Ident.str  in
               add_one1 env se uu____13992
           | uu____13994 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14016) ->
          add_sigelts env ses
      | uu____14025 ->
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
            | uu____14040 -> ()))

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
        (fun uu___233_14071  ->
           match uu___233_14071 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____14089 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____14150,lb::[]),uu____14152) ->
            let uu____14159 =
              let uu____14168 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____14177 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____14168, uu____14177)  in
            FStar_Pervasives_Native.Some uu____14159
        | FStar_Syntax_Syntax.Sig_let ((uu____14190,lbs),uu____14192) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____14222 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____14234 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____14234
                     then
                       let uu____14245 =
                         let uu____14254 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____14263 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____14254, uu____14263)  in
                       FStar_Pervasives_Native.Some uu____14245
                     else FStar_Pervasives_Native.None)
        | uu____14285 -> FStar_Pervasives_Native.None
  
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
          let uu____14344 =
            let uu____14353 =
              let uu____14358 =
                let uu____14359 =
                  let uu____14362 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____14362
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____14359)  in
              inst_tscheme1 uu____14358  in
            (uu____14353, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____14344
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____14384,uu____14385) ->
          let uu____14390 =
            let uu____14399 =
              let uu____14404 =
                let uu____14405 =
                  let uu____14408 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____14408  in
                (us, uu____14405)  in
              inst_tscheme1 uu____14404  in
            (uu____14399, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____14390
      | uu____14427 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____14515 =
          match uu____14515 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____14611,uvs,t,uu____14614,uu____14615,uu____14616);
                      FStar_Syntax_Syntax.sigrng = uu____14617;
                      FStar_Syntax_Syntax.sigquals = uu____14618;
                      FStar_Syntax_Syntax.sigmeta = uu____14619;
                      FStar_Syntax_Syntax.sigattrs = uu____14620;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____14641 =
                     let uu____14650 = inst_tscheme1 (uvs, t)  in
                     (uu____14650, rng)  in
                   FStar_Pervasives_Native.Some uu____14641
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____14674;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____14676;
                      FStar_Syntax_Syntax.sigattrs = uu____14677;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____14694 =
                     let uu____14695 = in_cur_mod env l  in uu____14695 = Yes
                      in
                   if uu____14694
                   then
                     let uu____14706 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____14706
                      then
                        let uu____14719 =
                          let uu____14728 = inst_tscheme1 (uvs, t)  in
                          (uu____14728, rng)  in
                        FStar_Pervasives_Native.Some uu____14719
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____14759 =
                        let uu____14768 = inst_tscheme1 (uvs, t)  in
                        (uu____14768, rng)  in
                      FStar_Pervasives_Native.Some uu____14759)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14793,uu____14794);
                      FStar_Syntax_Syntax.sigrng = uu____14795;
                      FStar_Syntax_Syntax.sigquals = uu____14796;
                      FStar_Syntax_Syntax.sigmeta = uu____14797;
                      FStar_Syntax_Syntax.sigattrs = uu____14798;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____14839 =
                          let uu____14848 = inst_tscheme1 (uvs, k)  in
                          (uu____14848, rng)  in
                        FStar_Pervasives_Native.Some uu____14839
                    | uu____14869 ->
                        let uu____14870 =
                          let uu____14879 =
                            let uu____14884 =
                              let uu____14885 =
                                let uu____14888 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14888
                                 in
                              (uvs, uu____14885)  in
                            inst_tscheme1 uu____14884  in
                          (uu____14879, rng)  in
                        FStar_Pervasives_Native.Some uu____14870)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14911,uu____14912);
                      FStar_Syntax_Syntax.sigrng = uu____14913;
                      FStar_Syntax_Syntax.sigquals = uu____14914;
                      FStar_Syntax_Syntax.sigmeta = uu____14915;
                      FStar_Syntax_Syntax.sigattrs = uu____14916;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14958 =
                          let uu____14967 = inst_tscheme_with (uvs, k) us  in
                          (uu____14967, rng)  in
                        FStar_Pervasives_Native.Some uu____14958
                    | uu____14988 ->
                        let uu____14989 =
                          let uu____14998 =
                            let uu____15003 =
                              let uu____15004 =
                                let uu____15007 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____15007
                                 in
                              (uvs, uu____15004)  in
                            inst_tscheme_with uu____15003 us  in
                          (uu____14998, rng)  in
                        FStar_Pervasives_Native.Some uu____14989)
               | FStar_Util.Inr se ->
                   let uu____15043 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____15064;
                          FStar_Syntax_Syntax.sigrng = uu____15065;
                          FStar_Syntax_Syntax.sigquals = uu____15066;
                          FStar_Syntax_Syntax.sigmeta = uu____15067;
                          FStar_Syntax_Syntax.sigattrs = uu____15068;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____15083 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____15043
                     (FStar_Util.map_option
                        (fun uu____15131  ->
                           match uu____15131 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____15162 =
          let uu____15173 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____15173 mapper  in
        match uu____15162 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____15247 =
              let uu____15258 =
                let uu____15265 =
                  let uu___253_15268 = t  in
                  let uu____15269 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___253_15268.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____15269;
                    FStar_Syntax_Syntax.vars =
                      (uu___253_15268.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____15265)  in
              (uu____15258, r)  in
            FStar_Pervasives_Native.Some uu____15247
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____15316 = lookup_qname env l  in
      match uu____15316 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____15335 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____15387 = try_lookup_bv env bv  in
      match uu____15387 with
      | FStar_Pervasives_Native.None  ->
          let uu____15402 = variable_not_found bv  in
          FStar_Errors.raise_error uu____15402 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____15417 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____15418 =
            let uu____15419 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____15419  in
          (uu____15417, uu____15418)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____15440 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____15440 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____15506 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____15506  in
          let uu____15507 =
            let uu____15516 =
              let uu____15521 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____15521)  in
            (uu____15516, r1)  in
          FStar_Pervasives_Native.Some uu____15507
  
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
        let uu____15555 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____15555 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____15588,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____15613 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____15613  in
            let uu____15614 =
              let uu____15619 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____15619, r1)  in
            FStar_Pervasives_Native.Some uu____15614
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____15642 = try_lookup_lid env l  in
      match uu____15642 with
      | FStar_Pervasives_Native.None  ->
          let uu____15669 = name_not_found l  in
          let uu____15674 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____15669 uu____15674
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___234_15714  ->
              match uu___234_15714 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____15716 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15735 = lookup_qname env lid  in
      match uu____15735 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15744,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15747;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15749;
              FStar_Syntax_Syntax.sigattrs = uu____15750;_},FStar_Pervasives_Native.None
            ),uu____15751)
          ->
          let uu____15800 =
            let uu____15807 =
              let uu____15808 =
                let uu____15811 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____15811 t  in
              (uvs, uu____15808)  in
            (uu____15807, q)  in
          FStar_Pervasives_Native.Some uu____15800
      | uu____15824 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15845 = lookup_qname env lid  in
      match uu____15845 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15850,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15853;
              FStar_Syntax_Syntax.sigquals = uu____15854;
              FStar_Syntax_Syntax.sigmeta = uu____15855;
              FStar_Syntax_Syntax.sigattrs = uu____15856;_},FStar_Pervasives_Native.None
            ),uu____15857)
          ->
          let uu____15906 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15906 (uvs, t)
      | uu____15911 ->
          let uu____15912 = name_not_found lid  in
          let uu____15917 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15912 uu____15917
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15936 = lookup_qname env lid  in
      match uu____15936 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15941,uvs,t,uu____15944,uu____15945,uu____15946);
              FStar_Syntax_Syntax.sigrng = uu____15947;
              FStar_Syntax_Syntax.sigquals = uu____15948;
              FStar_Syntax_Syntax.sigmeta = uu____15949;
              FStar_Syntax_Syntax.sigattrs = uu____15950;_},FStar_Pervasives_Native.None
            ),uu____15951)
          ->
          let uu____16004 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____16004 (uvs, t)
      | uu____16009 ->
          let uu____16010 = name_not_found lid  in
          let uu____16015 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____16010 uu____16015
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____16036 = lookup_qname env lid  in
      match uu____16036 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16043,uu____16044,uu____16045,uu____16046,uu____16047,dcs);
              FStar_Syntax_Syntax.sigrng = uu____16049;
              FStar_Syntax_Syntax.sigquals = uu____16050;
              FStar_Syntax_Syntax.sigmeta = uu____16051;
              FStar_Syntax_Syntax.sigattrs = uu____16052;_},uu____16053),uu____16054)
          -> (true, dcs)
      | uu____16115 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____16128 = lookup_qname env lid  in
      match uu____16128 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16129,uu____16130,uu____16131,l,uu____16133,uu____16134);
              FStar_Syntax_Syntax.sigrng = uu____16135;
              FStar_Syntax_Syntax.sigquals = uu____16136;
              FStar_Syntax_Syntax.sigmeta = uu____16137;
              FStar_Syntax_Syntax.sigattrs = uu____16138;_},uu____16139),uu____16140)
          -> l
      | uu____16195 ->
          let uu____16196 =
            let uu____16197 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____16197  in
          failwith uu____16196
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____16259)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____16316) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____16338 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____16338
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____16370 -> FStar_Pervasives_Native.None)
          | uu____16379 -> FStar_Pervasives_Native.None
  
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
        let uu____16438 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____16438
  
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
        let uu____16470 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____16470
  
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
             (FStar_Util.Inl uu____16515,uu____16516) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____16564),uu____16565) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____16614 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____16631 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____16640 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____16655 ->
                  let uu____16662 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____16662
              | FStar_Syntax_Syntax.Sig_let ((uu____16663,lbs),uu____16665)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____16679 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____16679
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____16683 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____16690 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____16691 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____16698 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16699 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____16700 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16701 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____16714 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____16727 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____16727
           (fun d_opt  ->
              let uu____16739 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____16739
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____16745 =
                   let uu____16748 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____16748  in
                 match uu____16745 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____16749 =
                       let uu____16750 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____16750
                        in
                     failwith uu____16749
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____16753 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____16753
                       then
                         let uu____16754 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____16755 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____16756 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____16754 uu____16755 uu____16756
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
        (FStar_Util.Inr (se,uu____16777),uu____16778) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____16827 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____16848),uu____16849) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____16898 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____16919 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____16919
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____16939 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____16939 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____16959 =
                      let uu____16960 = FStar_Syntax_Util.un_uinst tm  in
                      uu____16960.FStar_Syntax_Syntax.n  in
                    match uu____16959 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____16964 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____16979 = lookup_qname env ftv  in
      match uu____16979 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____16983) ->
          let uu____17028 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____17028 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____17049,t),r) ->
               let uu____17064 =
                 let uu____17065 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____17065 t  in
               FStar_Pervasives_Native.Some uu____17064)
      | uu____17066 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____17077 = try_lookup_effect_lid env ftv  in
      match uu____17077 with
      | FStar_Pervasives_Native.None  ->
          let uu____17080 = name_not_found ftv  in
          let uu____17085 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____17080 uu____17085
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
        let uu____17108 = lookup_qname env lid0  in
        match uu____17108 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____17119);
                FStar_Syntax_Syntax.sigrng = uu____17120;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____17122;
                FStar_Syntax_Syntax.sigattrs = uu____17123;_},FStar_Pervasives_Native.None
              ),uu____17124)
            ->
            let lid1 =
              let uu____17178 =
                let uu____17179 = FStar_Ident.range_of_lid lid  in
                let uu____17180 =
                  let uu____17181 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____17181  in
                FStar_Range.set_use_range uu____17179 uu____17180  in
              FStar_Ident.set_lid_range lid uu____17178  in
            let uu____17182 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___235_17186  ->
                      match uu___235_17186 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____17187 -> false))
               in
            if uu____17182
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____17201 =
                      let uu____17202 =
                        let uu____17203 = get_range env  in
                        FStar_Range.string_of_range uu____17203  in
                      let uu____17204 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____17205 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____17202 uu____17204 uu____17205
                       in
                    failwith uu____17201)
                  in
               match (binders, univs1) with
               | ([],uu____17222) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____17247,uu____17248::uu____17249::uu____17250) ->
                   let uu____17271 =
                     let uu____17272 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____17273 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____17272 uu____17273
                      in
                   failwith uu____17271
               | uu____17280 ->
                   let uu____17295 =
                     let uu____17300 =
                       let uu____17301 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____17301)  in
                     inst_tscheme_with uu____17300 insts  in
                   (match uu____17295 with
                    | (uu____17314,t) ->
                        let t1 =
                          let uu____17317 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____17317 t  in
                        let uu____17318 =
                          let uu____17319 = FStar_Syntax_Subst.compress t1
                             in
                          uu____17319.FStar_Syntax_Syntax.n  in
                        (match uu____17318 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____17354 -> failwith "Impossible")))
        | uu____17361 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____17384 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____17384 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____17397,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____17404 = find1 l2  in
            (match uu____17404 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____17411 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____17411 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____17415 = find1 l  in
            (match uu____17415 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____17420 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____17420
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____17434 = lookup_qname env l1  in
      match uu____17434 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____17437;
              FStar_Syntax_Syntax.sigrng = uu____17438;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17440;
              FStar_Syntax_Syntax.sigattrs = uu____17441;_},uu____17442),uu____17443)
          -> q
      | uu____17494 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____17515 =
          let uu____17516 =
            let uu____17517 = FStar_Util.string_of_int i  in
            let uu____17518 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____17517 uu____17518
             in
          failwith uu____17516  in
        let uu____17519 = lookup_datacon env lid  in
        match uu____17519 with
        | (uu____17524,t) ->
            let uu____17526 =
              let uu____17527 = FStar_Syntax_Subst.compress t  in
              uu____17527.FStar_Syntax_Syntax.n  in
            (match uu____17526 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17531) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____17572 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____17572
                      FStar_Pervasives_Native.fst)
             | uu____17583 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17594 = lookup_qname env l  in
      match uu____17594 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17595,uu____17596,uu____17597);
              FStar_Syntax_Syntax.sigrng = uu____17598;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____17600;
              FStar_Syntax_Syntax.sigattrs = uu____17601;_},uu____17602),uu____17603)
          ->
          FStar_Util.for_some
            (fun uu___236_17656  ->
               match uu___236_17656 with
               | FStar_Syntax_Syntax.Projector uu____17657 -> true
               | uu____17662 -> false) quals
      | uu____17663 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17674 = lookup_qname env lid  in
      match uu____17674 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17675,uu____17676,uu____17677,uu____17678,uu____17679,uu____17680);
              FStar_Syntax_Syntax.sigrng = uu____17681;
              FStar_Syntax_Syntax.sigquals = uu____17682;
              FStar_Syntax_Syntax.sigmeta = uu____17683;
              FStar_Syntax_Syntax.sigattrs = uu____17684;_},uu____17685),uu____17686)
          -> true
      | uu____17741 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17752 = lookup_qname env lid  in
      match uu____17752 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17753,uu____17754,uu____17755,uu____17756,uu____17757,uu____17758);
              FStar_Syntax_Syntax.sigrng = uu____17759;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____17761;
              FStar_Syntax_Syntax.sigattrs = uu____17762;_},uu____17763),uu____17764)
          ->
          FStar_Util.for_some
            (fun uu___237_17825  ->
               match uu___237_17825 with
               | FStar_Syntax_Syntax.RecordType uu____17826 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____17835 -> true
               | uu____17844 -> false) quals
      | uu____17845 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____17851,uu____17852);
            FStar_Syntax_Syntax.sigrng = uu____17853;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____17855;
            FStar_Syntax_Syntax.sigattrs = uu____17856;_},uu____17857),uu____17858)
        ->
        FStar_Util.for_some
          (fun uu___238_17915  ->
             match uu___238_17915 with
             | FStar_Syntax_Syntax.Action uu____17916 -> true
             | uu____17917 -> false) quals
    | uu____17918 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17929 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____17929
  
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
      let uu____17943 =
        let uu____17944 = FStar_Syntax_Util.un_uinst head1  in
        uu____17944.FStar_Syntax_Syntax.n  in
      match uu____17943 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____17948 ->
               true
           | uu____17949 -> false)
      | uu____17950 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17961 = lookup_qname env l  in
      match uu____17961 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____17963),uu____17964) ->
          FStar_Util.for_some
            (fun uu___239_18012  ->
               match uu___239_18012 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____18013 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____18014 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____18085 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____18101) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____18118 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____18125 ->
                 FStar_Pervasives_Native.Some true
             | uu____18142 -> FStar_Pervasives_Native.Some false)
         in
      let uu____18143 =
        let uu____18146 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____18146 mapper  in
      match uu____18143 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____18198 = lookup_qname env lid  in
      match uu____18198 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18201,uu____18202,tps,uu____18204,uu____18205,uu____18206);
              FStar_Syntax_Syntax.sigrng = uu____18207;
              FStar_Syntax_Syntax.sigquals = uu____18208;
              FStar_Syntax_Syntax.sigmeta = uu____18209;
              FStar_Syntax_Syntax.sigattrs = uu____18210;_},uu____18211),uu____18212)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____18277 -> FStar_Pervasives_Native.None
  
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
           (fun uu____18321  ->
              match uu____18321 with
              | (d,uu____18329) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____18344 = effect_decl_opt env l  in
      match uu____18344 with
      | FStar_Pervasives_Native.None  ->
          let uu____18359 = name_not_found l  in
          let uu____18364 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18359 uu____18364
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____18386  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____18405  ->
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
        let uu____18436 = FStar_Ident.lid_equals l1 l2  in
        if uu____18436
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____18444 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____18444
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____18452 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____18505  ->
                        match uu____18505 with
                        | (m1,m2,uu____18518,uu____18519,uu____18520) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____18452 with
              | FStar_Pervasives_Native.None  ->
                  let uu____18537 =
                    let uu____18542 =
                      let uu____18543 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____18544 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____18543
                        uu____18544
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____18542)
                     in
                  FStar_Errors.raise_error uu____18537 env.range
              | FStar_Pervasives_Native.Some
                  (uu____18551,uu____18552,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____18585 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____18585
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
  'Auu____18601 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____18601)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____18630 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____18656  ->
                match uu____18656 with
                | (d,uu____18662) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____18630 with
      | FStar_Pervasives_Native.None  ->
          let uu____18673 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____18673
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____18686 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____18686 with
           | (uu____18701,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____18719)::(wp,uu____18721)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____18777 -> failwith "Impossible"))
  
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
          let uu____18832 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____18832
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____18834 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____18834
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
                  let uu____18842 = get_range env  in
                  let uu____18843 =
                    let uu____18850 =
                      let uu____18851 =
                        let uu____18868 =
                          let uu____18879 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____18879]  in
                        (null_wp, uu____18868)  in
                      FStar_Syntax_Syntax.Tm_app uu____18851  in
                    FStar_Syntax_Syntax.mk uu____18850  in
                  uu____18843 FStar_Pervasives_Native.None uu____18842  in
                let uu____18919 =
                  let uu____18920 =
                    let uu____18931 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____18931]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____18920;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____18919))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___254_18968 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___254_18968.order);
              joins = (uu___254_18968.joins)
            }  in
          let uu___255_18977 = env  in
          {
            solver = (uu___255_18977.solver);
            range = (uu___255_18977.range);
            curmodule = (uu___255_18977.curmodule);
            gamma = (uu___255_18977.gamma);
            gamma_sig = (uu___255_18977.gamma_sig);
            gamma_cache = (uu___255_18977.gamma_cache);
            modules = (uu___255_18977.modules);
            expected_typ = (uu___255_18977.expected_typ);
            sigtab = (uu___255_18977.sigtab);
            attrtab = (uu___255_18977.attrtab);
            is_pattern = (uu___255_18977.is_pattern);
            instantiate_imp = (uu___255_18977.instantiate_imp);
            effects;
            generalize = (uu___255_18977.generalize);
            letrecs = (uu___255_18977.letrecs);
            top_level = (uu___255_18977.top_level);
            check_uvars = (uu___255_18977.check_uvars);
            use_eq = (uu___255_18977.use_eq);
            is_iface = (uu___255_18977.is_iface);
            admit = (uu___255_18977.admit);
            lax = (uu___255_18977.lax);
            lax_universes = (uu___255_18977.lax_universes);
            phase1 = (uu___255_18977.phase1);
            failhard = (uu___255_18977.failhard);
            nosynth = (uu___255_18977.nosynth);
            uvar_subtyping = (uu___255_18977.uvar_subtyping);
            tc_term = (uu___255_18977.tc_term);
            type_of = (uu___255_18977.type_of);
            universe_of = (uu___255_18977.universe_of);
            check_type_of = (uu___255_18977.check_type_of);
            use_bv_sorts = (uu___255_18977.use_bv_sorts);
            qtbl_name_and_index = (uu___255_18977.qtbl_name_and_index);
            normalized_eff_names = (uu___255_18977.normalized_eff_names);
            fv_delta_depths = (uu___255_18977.fv_delta_depths);
            proof_ns = (uu___255_18977.proof_ns);
            synth_hook = (uu___255_18977.synth_hook);
            splice = (uu___255_18977.splice);
            postprocess = (uu___255_18977.postprocess);
            is_native_tactic = (uu___255_18977.is_native_tactic);
            identifier_info = (uu___255_18977.identifier_info);
            tc_hooks = (uu___255_18977.tc_hooks);
            dsenv = (uu___255_18977.dsenv);
            nbe = (uu___255_18977.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____19007 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____19007  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____19165 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____19166 = l1 u t wp e  in
                                l2 u t uu____19165 uu____19166))
                | uu____19167 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____19239 = inst_tscheme_with lift_t [u]  in
            match uu____19239 with
            | (uu____19246,lift_t1) ->
                let uu____19248 =
                  let uu____19255 =
                    let uu____19256 =
                      let uu____19273 =
                        let uu____19284 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____19293 =
                          let uu____19304 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____19304]  in
                        uu____19284 :: uu____19293  in
                      (lift_t1, uu____19273)  in
                    FStar_Syntax_Syntax.Tm_app uu____19256  in
                  FStar_Syntax_Syntax.mk uu____19255  in
                uu____19248 FStar_Pervasives_Native.None
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
            let uu____19416 = inst_tscheme_with lift_t [u]  in
            match uu____19416 with
            | (uu____19423,lift_t1) ->
                let uu____19425 =
                  let uu____19432 =
                    let uu____19433 =
                      let uu____19450 =
                        let uu____19461 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____19470 =
                          let uu____19481 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____19490 =
                            let uu____19501 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____19501]  in
                          uu____19481 :: uu____19490  in
                        uu____19461 :: uu____19470  in
                      (lift_t1, uu____19450)  in
                    FStar_Syntax_Syntax.Tm_app uu____19433  in
                  FStar_Syntax_Syntax.mk uu____19432  in
                uu____19425 FStar_Pervasives_Native.None
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
              let uu____19603 =
                let uu____19604 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____19604
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____19603  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____19608 =
              let uu____19609 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____19609  in
            let uu____19610 =
              let uu____19611 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____19637 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____19637)
                 in
              FStar_Util.dflt "none" uu____19611  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____19608
              uu____19610
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____19663  ->
                    match uu____19663 with
                    | (e,uu____19671) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____19694 =
            match uu____19694 with
            | (i,j) ->
                let uu____19705 = FStar_Ident.lid_equals i j  in
                if uu____19705
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
              let uu____19737 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____19747 = FStar_Ident.lid_equals i k  in
                        if uu____19747
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____19758 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____19758
                                  then []
                                  else
                                    (let uu____19762 =
                                       let uu____19771 =
                                         find_edge order1 (i, k)  in
                                       let uu____19774 =
                                         find_edge order1 (k, j)  in
                                       (uu____19771, uu____19774)  in
                                     match uu____19762 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____19789 =
                                           compose_edges e1 e2  in
                                         [uu____19789]
                                     | uu____19790 -> [])))))
                 in
              FStar_List.append order1 uu____19737  in
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
                   let uu____19820 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____19822 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____19822
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____19820
                   then
                     let uu____19827 =
                       let uu____19832 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____19832)
                        in
                     let uu____19833 = get_range env  in
                     FStar_Errors.raise_error uu____19827 uu____19833
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____19910 = FStar_Ident.lid_equals i j
                                   in
                                if uu____19910
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____19959 =
                                              let uu____19968 =
                                                find_edge order2 (i, k)  in
                                              let uu____19971 =
                                                find_edge order2 (j, k)  in
                                              (uu____19968, uu____19971)  in
                                            match uu____19959 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____20013,uu____20014)
                                                     ->
                                                     let uu____20021 =
                                                       let uu____20026 =
                                                         let uu____20027 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____20027
                                                          in
                                                       let uu____20030 =
                                                         let uu____20031 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____20031
                                                          in
                                                       (uu____20026,
                                                         uu____20030)
                                                        in
                                                     (match uu____20021 with
                                                      | (true ,true ) ->
                                                          let uu____20042 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____20042
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
                                            | uu____20067 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___256_20140 = env.effects  in
              { decls = (uu___256_20140.decls); order = order2; joins }  in
            let uu___257_20141 = env  in
            {
              solver = (uu___257_20141.solver);
              range = (uu___257_20141.range);
              curmodule = (uu___257_20141.curmodule);
              gamma = (uu___257_20141.gamma);
              gamma_sig = (uu___257_20141.gamma_sig);
              gamma_cache = (uu___257_20141.gamma_cache);
              modules = (uu___257_20141.modules);
              expected_typ = (uu___257_20141.expected_typ);
              sigtab = (uu___257_20141.sigtab);
              attrtab = (uu___257_20141.attrtab);
              is_pattern = (uu___257_20141.is_pattern);
              instantiate_imp = (uu___257_20141.instantiate_imp);
              effects;
              generalize = (uu___257_20141.generalize);
              letrecs = (uu___257_20141.letrecs);
              top_level = (uu___257_20141.top_level);
              check_uvars = (uu___257_20141.check_uvars);
              use_eq = (uu___257_20141.use_eq);
              is_iface = (uu___257_20141.is_iface);
              admit = (uu___257_20141.admit);
              lax = (uu___257_20141.lax);
              lax_universes = (uu___257_20141.lax_universes);
              phase1 = (uu___257_20141.phase1);
              failhard = (uu___257_20141.failhard);
              nosynth = (uu___257_20141.nosynth);
              uvar_subtyping = (uu___257_20141.uvar_subtyping);
              tc_term = (uu___257_20141.tc_term);
              type_of = (uu___257_20141.type_of);
              universe_of = (uu___257_20141.universe_of);
              check_type_of = (uu___257_20141.check_type_of);
              use_bv_sorts = (uu___257_20141.use_bv_sorts);
              qtbl_name_and_index = (uu___257_20141.qtbl_name_and_index);
              normalized_eff_names = (uu___257_20141.normalized_eff_names);
              fv_delta_depths = (uu___257_20141.fv_delta_depths);
              proof_ns = (uu___257_20141.proof_ns);
              synth_hook = (uu___257_20141.synth_hook);
              splice = (uu___257_20141.splice);
              postprocess = (uu___257_20141.postprocess);
              is_native_tactic = (uu___257_20141.is_native_tactic);
              identifier_info = (uu___257_20141.identifier_info);
              tc_hooks = (uu___257_20141.tc_hooks);
              dsenv = (uu___257_20141.dsenv);
              nbe = (uu___257_20141.nbe)
            }))
      | uu____20142 -> env
  
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
        | uu____20170 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____20182 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____20182 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____20199 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____20199 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____20221 =
                     let uu____20226 =
                       let uu____20227 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____20234 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____20243 =
                         let uu____20244 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____20244  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____20227 uu____20234 uu____20243
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____20226)
                      in
                   FStar_Errors.raise_error uu____20221
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____20249 =
                     let uu____20260 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____20260 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____20297  ->
                        fun uu____20298  ->
                          match (uu____20297, uu____20298) with
                          | ((x,uu____20328),(t,uu____20330)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____20249
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____20361 =
                     let uu___258_20362 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___258_20362.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___258_20362.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___258_20362.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___258_20362.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____20361
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____20373 .
    'Auu____20373 ->
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
          let uu____20403 = effect_decl_opt env effect_name  in
          match uu____20403 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____20442 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____20465 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____20502 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____20502
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____20503 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____20503
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____20517 =
                     let uu____20520 = get_range env  in
                     let uu____20521 =
                       let uu____20528 =
                         let uu____20529 =
                           let uu____20546 =
                             let uu____20557 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____20557; wp]  in
                           (repr, uu____20546)  in
                         FStar_Syntax_Syntax.Tm_app uu____20529  in
                       FStar_Syntax_Syntax.mk uu____20528  in
                     uu____20521 FStar_Pervasives_Native.None uu____20520  in
                   FStar_Pervasives_Native.Some uu____20517)
  
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
      | uu____20672 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20683 =
        let uu____20684 = FStar_Syntax_Subst.compress t  in
        uu____20684.FStar_Syntax_Syntax.n  in
      match uu____20683 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____20687,c) ->
          is_reifiable_comp env c
      | uu____20709 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____20727 =
           let uu____20728 = is_reifiable_effect env l  in
           Prims.op_Negation uu____20728  in
         if uu____20727
         then
           let uu____20729 =
             let uu____20734 =
               let uu____20735 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____20735
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____20734)  in
           let uu____20736 = get_range env  in
           FStar_Errors.raise_error uu____20729 uu____20736
         else ());
        (let uu____20738 = effect_repr_aux true env c u_c  in
         match uu____20738 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___259_20770 = env  in
        {
          solver = (uu___259_20770.solver);
          range = (uu___259_20770.range);
          curmodule = (uu___259_20770.curmodule);
          gamma = (uu___259_20770.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___259_20770.gamma_cache);
          modules = (uu___259_20770.modules);
          expected_typ = (uu___259_20770.expected_typ);
          sigtab = (uu___259_20770.sigtab);
          attrtab = (uu___259_20770.attrtab);
          is_pattern = (uu___259_20770.is_pattern);
          instantiate_imp = (uu___259_20770.instantiate_imp);
          effects = (uu___259_20770.effects);
          generalize = (uu___259_20770.generalize);
          letrecs = (uu___259_20770.letrecs);
          top_level = (uu___259_20770.top_level);
          check_uvars = (uu___259_20770.check_uvars);
          use_eq = (uu___259_20770.use_eq);
          is_iface = (uu___259_20770.is_iface);
          admit = (uu___259_20770.admit);
          lax = (uu___259_20770.lax);
          lax_universes = (uu___259_20770.lax_universes);
          phase1 = (uu___259_20770.phase1);
          failhard = (uu___259_20770.failhard);
          nosynth = (uu___259_20770.nosynth);
          uvar_subtyping = (uu___259_20770.uvar_subtyping);
          tc_term = (uu___259_20770.tc_term);
          type_of = (uu___259_20770.type_of);
          universe_of = (uu___259_20770.universe_of);
          check_type_of = (uu___259_20770.check_type_of);
          use_bv_sorts = (uu___259_20770.use_bv_sorts);
          qtbl_name_and_index = (uu___259_20770.qtbl_name_and_index);
          normalized_eff_names = (uu___259_20770.normalized_eff_names);
          fv_delta_depths = (uu___259_20770.fv_delta_depths);
          proof_ns = (uu___259_20770.proof_ns);
          synth_hook = (uu___259_20770.synth_hook);
          splice = (uu___259_20770.splice);
          postprocess = (uu___259_20770.postprocess);
          is_native_tactic = (uu___259_20770.is_native_tactic);
          identifier_info = (uu___259_20770.identifier_info);
          tc_hooks = (uu___259_20770.tc_hooks);
          dsenv = (uu___259_20770.dsenv);
          nbe = (uu___259_20770.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___260_20783 = env  in
      {
        solver = (uu___260_20783.solver);
        range = (uu___260_20783.range);
        curmodule = (uu___260_20783.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___260_20783.gamma_sig);
        gamma_cache = (uu___260_20783.gamma_cache);
        modules = (uu___260_20783.modules);
        expected_typ = (uu___260_20783.expected_typ);
        sigtab = (uu___260_20783.sigtab);
        attrtab = (uu___260_20783.attrtab);
        is_pattern = (uu___260_20783.is_pattern);
        instantiate_imp = (uu___260_20783.instantiate_imp);
        effects = (uu___260_20783.effects);
        generalize = (uu___260_20783.generalize);
        letrecs = (uu___260_20783.letrecs);
        top_level = (uu___260_20783.top_level);
        check_uvars = (uu___260_20783.check_uvars);
        use_eq = (uu___260_20783.use_eq);
        is_iface = (uu___260_20783.is_iface);
        admit = (uu___260_20783.admit);
        lax = (uu___260_20783.lax);
        lax_universes = (uu___260_20783.lax_universes);
        phase1 = (uu___260_20783.phase1);
        failhard = (uu___260_20783.failhard);
        nosynth = (uu___260_20783.nosynth);
        uvar_subtyping = (uu___260_20783.uvar_subtyping);
        tc_term = (uu___260_20783.tc_term);
        type_of = (uu___260_20783.type_of);
        universe_of = (uu___260_20783.universe_of);
        check_type_of = (uu___260_20783.check_type_of);
        use_bv_sorts = (uu___260_20783.use_bv_sorts);
        qtbl_name_and_index = (uu___260_20783.qtbl_name_and_index);
        normalized_eff_names = (uu___260_20783.normalized_eff_names);
        fv_delta_depths = (uu___260_20783.fv_delta_depths);
        proof_ns = (uu___260_20783.proof_ns);
        synth_hook = (uu___260_20783.synth_hook);
        splice = (uu___260_20783.splice);
        postprocess = (uu___260_20783.postprocess);
        is_native_tactic = (uu___260_20783.is_native_tactic);
        identifier_info = (uu___260_20783.identifier_info);
        tc_hooks = (uu___260_20783.tc_hooks);
        dsenv = (uu___260_20783.dsenv);
        nbe = (uu___260_20783.nbe)
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
            (let uu___261_20838 = env  in
             {
               solver = (uu___261_20838.solver);
               range = (uu___261_20838.range);
               curmodule = (uu___261_20838.curmodule);
               gamma = rest;
               gamma_sig = (uu___261_20838.gamma_sig);
               gamma_cache = (uu___261_20838.gamma_cache);
               modules = (uu___261_20838.modules);
               expected_typ = (uu___261_20838.expected_typ);
               sigtab = (uu___261_20838.sigtab);
               attrtab = (uu___261_20838.attrtab);
               is_pattern = (uu___261_20838.is_pattern);
               instantiate_imp = (uu___261_20838.instantiate_imp);
               effects = (uu___261_20838.effects);
               generalize = (uu___261_20838.generalize);
               letrecs = (uu___261_20838.letrecs);
               top_level = (uu___261_20838.top_level);
               check_uvars = (uu___261_20838.check_uvars);
               use_eq = (uu___261_20838.use_eq);
               is_iface = (uu___261_20838.is_iface);
               admit = (uu___261_20838.admit);
               lax = (uu___261_20838.lax);
               lax_universes = (uu___261_20838.lax_universes);
               phase1 = (uu___261_20838.phase1);
               failhard = (uu___261_20838.failhard);
               nosynth = (uu___261_20838.nosynth);
               uvar_subtyping = (uu___261_20838.uvar_subtyping);
               tc_term = (uu___261_20838.tc_term);
               type_of = (uu___261_20838.type_of);
               universe_of = (uu___261_20838.universe_of);
               check_type_of = (uu___261_20838.check_type_of);
               use_bv_sorts = (uu___261_20838.use_bv_sorts);
               qtbl_name_and_index = (uu___261_20838.qtbl_name_and_index);
               normalized_eff_names = (uu___261_20838.normalized_eff_names);
               fv_delta_depths = (uu___261_20838.fv_delta_depths);
               proof_ns = (uu___261_20838.proof_ns);
               synth_hook = (uu___261_20838.synth_hook);
               splice = (uu___261_20838.splice);
               postprocess = (uu___261_20838.postprocess);
               is_native_tactic = (uu___261_20838.is_native_tactic);
               identifier_info = (uu___261_20838.identifier_info);
               tc_hooks = (uu___261_20838.tc_hooks);
               dsenv = (uu___261_20838.dsenv);
               nbe = (uu___261_20838.nbe)
             }))
    | uu____20839 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____20867  ->
             match uu____20867 with | (x,uu____20875) -> push_bv env1 x) env
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
            let uu___262_20909 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___262_20909.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___262_20909.FStar_Syntax_Syntax.index);
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
      (let uu___263_20949 = env  in
       {
         solver = (uu___263_20949.solver);
         range = (uu___263_20949.range);
         curmodule = (uu___263_20949.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___263_20949.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___263_20949.sigtab);
         attrtab = (uu___263_20949.attrtab);
         is_pattern = (uu___263_20949.is_pattern);
         instantiate_imp = (uu___263_20949.instantiate_imp);
         effects = (uu___263_20949.effects);
         generalize = (uu___263_20949.generalize);
         letrecs = (uu___263_20949.letrecs);
         top_level = (uu___263_20949.top_level);
         check_uvars = (uu___263_20949.check_uvars);
         use_eq = (uu___263_20949.use_eq);
         is_iface = (uu___263_20949.is_iface);
         admit = (uu___263_20949.admit);
         lax = (uu___263_20949.lax);
         lax_universes = (uu___263_20949.lax_universes);
         phase1 = (uu___263_20949.phase1);
         failhard = (uu___263_20949.failhard);
         nosynth = (uu___263_20949.nosynth);
         uvar_subtyping = (uu___263_20949.uvar_subtyping);
         tc_term = (uu___263_20949.tc_term);
         type_of = (uu___263_20949.type_of);
         universe_of = (uu___263_20949.universe_of);
         check_type_of = (uu___263_20949.check_type_of);
         use_bv_sorts = (uu___263_20949.use_bv_sorts);
         qtbl_name_and_index = (uu___263_20949.qtbl_name_and_index);
         normalized_eff_names = (uu___263_20949.normalized_eff_names);
         fv_delta_depths = (uu___263_20949.fv_delta_depths);
         proof_ns = (uu___263_20949.proof_ns);
         synth_hook = (uu___263_20949.synth_hook);
         splice = (uu___263_20949.splice);
         postprocess = (uu___263_20949.postprocess);
         is_native_tactic = (uu___263_20949.is_native_tactic);
         identifier_info = (uu___263_20949.identifier_info);
         tc_hooks = (uu___263_20949.tc_hooks);
         dsenv = (uu___263_20949.dsenv);
         nbe = (uu___263_20949.nbe)
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
        let uu____20991 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____20991 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____21019 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____21019)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___264_21034 = env  in
      {
        solver = (uu___264_21034.solver);
        range = (uu___264_21034.range);
        curmodule = (uu___264_21034.curmodule);
        gamma = (uu___264_21034.gamma);
        gamma_sig = (uu___264_21034.gamma_sig);
        gamma_cache = (uu___264_21034.gamma_cache);
        modules = (uu___264_21034.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___264_21034.sigtab);
        attrtab = (uu___264_21034.attrtab);
        is_pattern = (uu___264_21034.is_pattern);
        instantiate_imp = (uu___264_21034.instantiate_imp);
        effects = (uu___264_21034.effects);
        generalize = (uu___264_21034.generalize);
        letrecs = (uu___264_21034.letrecs);
        top_level = (uu___264_21034.top_level);
        check_uvars = (uu___264_21034.check_uvars);
        use_eq = false;
        is_iface = (uu___264_21034.is_iface);
        admit = (uu___264_21034.admit);
        lax = (uu___264_21034.lax);
        lax_universes = (uu___264_21034.lax_universes);
        phase1 = (uu___264_21034.phase1);
        failhard = (uu___264_21034.failhard);
        nosynth = (uu___264_21034.nosynth);
        uvar_subtyping = (uu___264_21034.uvar_subtyping);
        tc_term = (uu___264_21034.tc_term);
        type_of = (uu___264_21034.type_of);
        universe_of = (uu___264_21034.universe_of);
        check_type_of = (uu___264_21034.check_type_of);
        use_bv_sorts = (uu___264_21034.use_bv_sorts);
        qtbl_name_and_index = (uu___264_21034.qtbl_name_and_index);
        normalized_eff_names = (uu___264_21034.normalized_eff_names);
        fv_delta_depths = (uu___264_21034.fv_delta_depths);
        proof_ns = (uu___264_21034.proof_ns);
        synth_hook = (uu___264_21034.synth_hook);
        splice = (uu___264_21034.splice);
        postprocess = (uu___264_21034.postprocess);
        is_native_tactic = (uu___264_21034.is_native_tactic);
        identifier_info = (uu___264_21034.identifier_info);
        tc_hooks = (uu___264_21034.tc_hooks);
        dsenv = (uu___264_21034.dsenv);
        nbe = (uu___264_21034.nbe)
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
    let uu____21062 = expected_typ env_  in
    ((let uu___265_21068 = env_  in
      {
        solver = (uu___265_21068.solver);
        range = (uu___265_21068.range);
        curmodule = (uu___265_21068.curmodule);
        gamma = (uu___265_21068.gamma);
        gamma_sig = (uu___265_21068.gamma_sig);
        gamma_cache = (uu___265_21068.gamma_cache);
        modules = (uu___265_21068.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___265_21068.sigtab);
        attrtab = (uu___265_21068.attrtab);
        is_pattern = (uu___265_21068.is_pattern);
        instantiate_imp = (uu___265_21068.instantiate_imp);
        effects = (uu___265_21068.effects);
        generalize = (uu___265_21068.generalize);
        letrecs = (uu___265_21068.letrecs);
        top_level = (uu___265_21068.top_level);
        check_uvars = (uu___265_21068.check_uvars);
        use_eq = false;
        is_iface = (uu___265_21068.is_iface);
        admit = (uu___265_21068.admit);
        lax = (uu___265_21068.lax);
        lax_universes = (uu___265_21068.lax_universes);
        phase1 = (uu___265_21068.phase1);
        failhard = (uu___265_21068.failhard);
        nosynth = (uu___265_21068.nosynth);
        uvar_subtyping = (uu___265_21068.uvar_subtyping);
        tc_term = (uu___265_21068.tc_term);
        type_of = (uu___265_21068.type_of);
        universe_of = (uu___265_21068.universe_of);
        check_type_of = (uu___265_21068.check_type_of);
        use_bv_sorts = (uu___265_21068.use_bv_sorts);
        qtbl_name_and_index = (uu___265_21068.qtbl_name_and_index);
        normalized_eff_names = (uu___265_21068.normalized_eff_names);
        fv_delta_depths = (uu___265_21068.fv_delta_depths);
        proof_ns = (uu___265_21068.proof_ns);
        synth_hook = (uu___265_21068.synth_hook);
        splice = (uu___265_21068.splice);
        postprocess = (uu___265_21068.postprocess);
        is_native_tactic = (uu___265_21068.is_native_tactic);
        identifier_info = (uu___265_21068.identifier_info);
        tc_hooks = (uu___265_21068.tc_hooks);
        dsenv = (uu___265_21068.dsenv);
        nbe = (uu___265_21068.nbe)
      }), uu____21062)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____21078 =
      let uu____21081 = FStar_Ident.id_of_text ""  in [uu____21081]  in
    FStar_Ident.lid_of_ids uu____21078  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____21087 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____21087
        then
          let uu____21090 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____21090 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___266_21117 = env  in
       {
         solver = (uu___266_21117.solver);
         range = (uu___266_21117.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___266_21117.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___266_21117.expected_typ);
         sigtab = (uu___266_21117.sigtab);
         attrtab = (uu___266_21117.attrtab);
         is_pattern = (uu___266_21117.is_pattern);
         instantiate_imp = (uu___266_21117.instantiate_imp);
         effects = (uu___266_21117.effects);
         generalize = (uu___266_21117.generalize);
         letrecs = (uu___266_21117.letrecs);
         top_level = (uu___266_21117.top_level);
         check_uvars = (uu___266_21117.check_uvars);
         use_eq = (uu___266_21117.use_eq);
         is_iface = (uu___266_21117.is_iface);
         admit = (uu___266_21117.admit);
         lax = (uu___266_21117.lax);
         lax_universes = (uu___266_21117.lax_universes);
         phase1 = (uu___266_21117.phase1);
         failhard = (uu___266_21117.failhard);
         nosynth = (uu___266_21117.nosynth);
         uvar_subtyping = (uu___266_21117.uvar_subtyping);
         tc_term = (uu___266_21117.tc_term);
         type_of = (uu___266_21117.type_of);
         universe_of = (uu___266_21117.universe_of);
         check_type_of = (uu___266_21117.check_type_of);
         use_bv_sorts = (uu___266_21117.use_bv_sorts);
         qtbl_name_and_index = (uu___266_21117.qtbl_name_and_index);
         normalized_eff_names = (uu___266_21117.normalized_eff_names);
         fv_delta_depths = (uu___266_21117.fv_delta_depths);
         proof_ns = (uu___266_21117.proof_ns);
         synth_hook = (uu___266_21117.synth_hook);
         splice = (uu___266_21117.splice);
         postprocess = (uu___266_21117.postprocess);
         is_native_tactic = (uu___266_21117.is_native_tactic);
         identifier_info = (uu___266_21117.identifier_info);
         tc_hooks = (uu___266_21117.tc_hooks);
         dsenv = (uu___266_21117.dsenv);
         nbe = (uu___266_21117.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____21168)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____21172,(uu____21173,t)))::tl1
          ->
          let uu____21194 =
            let uu____21197 = FStar_Syntax_Free.uvars t  in
            ext out uu____21197  in
          aux uu____21194 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____21200;
            FStar_Syntax_Syntax.index = uu____21201;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____21208 =
            let uu____21211 = FStar_Syntax_Free.uvars t  in
            ext out uu____21211  in
          aux uu____21208 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____21268)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____21272,(uu____21273,t)))::tl1
          ->
          let uu____21294 =
            let uu____21297 = FStar_Syntax_Free.univs t  in
            ext out uu____21297  in
          aux uu____21294 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____21300;
            FStar_Syntax_Syntax.index = uu____21301;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____21308 =
            let uu____21311 = FStar_Syntax_Free.univs t  in
            ext out uu____21311  in
          aux uu____21308 tl1
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
          let uu____21372 = FStar_Util.set_add uname out  in
          aux uu____21372 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____21375,(uu____21376,t)))::tl1
          ->
          let uu____21397 =
            let uu____21400 = FStar_Syntax_Free.univnames t  in
            ext out uu____21400  in
          aux uu____21397 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____21403;
            FStar_Syntax_Syntax.index = uu____21404;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____21411 =
            let uu____21414 = FStar_Syntax_Free.univnames t  in
            ext out uu____21414  in
          aux uu____21411 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___240_21434  ->
            match uu___240_21434 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____21438 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____21451 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____21461 =
      let uu____21470 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____21470
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____21461 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____21514 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___241_21524  ->
              match uu___241_21524 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____21526 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____21526
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____21529) ->
                  let uu____21546 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____21546))
       in
    FStar_All.pipe_right uu____21514 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___242_21553  ->
    match uu___242_21553 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____21555 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____21555
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____21575  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____21617) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____21636,uu____21637) -> false  in
      let uu____21646 =
        FStar_List.tryFind
          (fun uu____21664  ->
             match uu____21664 with | (p,uu____21672) -> list_prefix p path)
          env.proof_ns
         in
      match uu____21646 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____21683,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21705 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____21705
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___267_21723 = e  in
        {
          solver = (uu___267_21723.solver);
          range = (uu___267_21723.range);
          curmodule = (uu___267_21723.curmodule);
          gamma = (uu___267_21723.gamma);
          gamma_sig = (uu___267_21723.gamma_sig);
          gamma_cache = (uu___267_21723.gamma_cache);
          modules = (uu___267_21723.modules);
          expected_typ = (uu___267_21723.expected_typ);
          sigtab = (uu___267_21723.sigtab);
          attrtab = (uu___267_21723.attrtab);
          is_pattern = (uu___267_21723.is_pattern);
          instantiate_imp = (uu___267_21723.instantiate_imp);
          effects = (uu___267_21723.effects);
          generalize = (uu___267_21723.generalize);
          letrecs = (uu___267_21723.letrecs);
          top_level = (uu___267_21723.top_level);
          check_uvars = (uu___267_21723.check_uvars);
          use_eq = (uu___267_21723.use_eq);
          is_iface = (uu___267_21723.is_iface);
          admit = (uu___267_21723.admit);
          lax = (uu___267_21723.lax);
          lax_universes = (uu___267_21723.lax_universes);
          phase1 = (uu___267_21723.phase1);
          failhard = (uu___267_21723.failhard);
          nosynth = (uu___267_21723.nosynth);
          uvar_subtyping = (uu___267_21723.uvar_subtyping);
          tc_term = (uu___267_21723.tc_term);
          type_of = (uu___267_21723.type_of);
          universe_of = (uu___267_21723.universe_of);
          check_type_of = (uu___267_21723.check_type_of);
          use_bv_sorts = (uu___267_21723.use_bv_sorts);
          qtbl_name_and_index = (uu___267_21723.qtbl_name_and_index);
          normalized_eff_names = (uu___267_21723.normalized_eff_names);
          fv_delta_depths = (uu___267_21723.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___267_21723.synth_hook);
          splice = (uu___267_21723.splice);
          postprocess = (uu___267_21723.postprocess);
          is_native_tactic = (uu___267_21723.is_native_tactic);
          identifier_info = (uu___267_21723.identifier_info);
          tc_hooks = (uu___267_21723.tc_hooks);
          dsenv = (uu___267_21723.dsenv);
          nbe = (uu___267_21723.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___268_21763 = e  in
      {
        solver = (uu___268_21763.solver);
        range = (uu___268_21763.range);
        curmodule = (uu___268_21763.curmodule);
        gamma = (uu___268_21763.gamma);
        gamma_sig = (uu___268_21763.gamma_sig);
        gamma_cache = (uu___268_21763.gamma_cache);
        modules = (uu___268_21763.modules);
        expected_typ = (uu___268_21763.expected_typ);
        sigtab = (uu___268_21763.sigtab);
        attrtab = (uu___268_21763.attrtab);
        is_pattern = (uu___268_21763.is_pattern);
        instantiate_imp = (uu___268_21763.instantiate_imp);
        effects = (uu___268_21763.effects);
        generalize = (uu___268_21763.generalize);
        letrecs = (uu___268_21763.letrecs);
        top_level = (uu___268_21763.top_level);
        check_uvars = (uu___268_21763.check_uvars);
        use_eq = (uu___268_21763.use_eq);
        is_iface = (uu___268_21763.is_iface);
        admit = (uu___268_21763.admit);
        lax = (uu___268_21763.lax);
        lax_universes = (uu___268_21763.lax_universes);
        phase1 = (uu___268_21763.phase1);
        failhard = (uu___268_21763.failhard);
        nosynth = (uu___268_21763.nosynth);
        uvar_subtyping = (uu___268_21763.uvar_subtyping);
        tc_term = (uu___268_21763.tc_term);
        type_of = (uu___268_21763.type_of);
        universe_of = (uu___268_21763.universe_of);
        check_type_of = (uu___268_21763.check_type_of);
        use_bv_sorts = (uu___268_21763.use_bv_sorts);
        qtbl_name_and_index = (uu___268_21763.qtbl_name_and_index);
        normalized_eff_names = (uu___268_21763.normalized_eff_names);
        fv_delta_depths = (uu___268_21763.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___268_21763.synth_hook);
        splice = (uu___268_21763.splice);
        postprocess = (uu___268_21763.postprocess);
        is_native_tactic = (uu___268_21763.is_native_tactic);
        identifier_info = (uu___268_21763.identifier_info);
        tc_hooks = (uu___268_21763.tc_hooks);
        dsenv = (uu___268_21763.dsenv);
        nbe = (uu___268_21763.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____21778 = FStar_Syntax_Free.names t  in
      let uu____21781 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____21778 uu____21781
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____21802 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____21802
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____21810 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____21810
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____21827 =
      match uu____21827 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____21837 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____21837)
       in
    let uu____21839 =
      let uu____21842 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____21842 FStar_List.rev  in
    FStar_All.pipe_right uu____21839 (FStar_String.concat " ")
  
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
                  (let uu____21895 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____21895 with
                   | FStar_Pervasives_Native.Some uu____21898 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____21899 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____21905;
        univ_ineqs = uu____21906; implicits = uu____21907;_} -> true
    | uu____21918 -> false
  
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
          let uu___269_21945 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___269_21945.deferred);
            univ_ineqs = (uu___269_21945.univ_ineqs);
            implicits = (uu___269_21945.implicits)
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
          let uu____21980 = FStar_Options.defensive ()  in
          if uu____21980
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____21984 =
              let uu____21985 =
                let uu____21986 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____21986  in
              Prims.op_Negation uu____21985  in
            (if uu____21984
             then
               let uu____21991 =
                 let uu____21996 =
                   let uu____21997 = FStar_Syntax_Print.term_to_string t  in
                   let uu____21998 =
                     let uu____21999 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____21999
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____21997 uu____21998
                    in
                 (FStar_Errors.Warning_Defensive, uu____21996)  in
               FStar_Errors.log_issue rng uu____21991
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
          let uu____22030 =
            let uu____22031 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____22031  in
          if uu____22030
          then ()
          else
            (let uu____22033 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____22033 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____22056 =
            let uu____22057 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____22057  in
          if uu____22056
          then ()
          else
            (let uu____22059 = bound_vars e  in
             def_check_closed_in rng msg uu____22059 t)
  
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
          let uu___270_22094 = g  in
          let uu____22095 =
            let uu____22096 =
              let uu____22097 =
                let uu____22104 =
                  let uu____22105 =
                    let uu____22122 =
                      let uu____22133 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____22133]  in
                    (f, uu____22122)  in
                  FStar_Syntax_Syntax.Tm_app uu____22105  in
                FStar_Syntax_Syntax.mk uu____22104  in
              uu____22097 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____22096
             in
          {
            guard_f = uu____22095;
            deferred = (uu___270_22094.deferred);
            univ_ineqs = (uu___270_22094.univ_ineqs);
            implicits = (uu___270_22094.implicits)
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
          let uu___271_22189 = g  in
          let uu____22190 =
            let uu____22191 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____22191  in
          {
            guard_f = uu____22190;
            deferred = (uu___271_22189.deferred);
            univ_ineqs = (uu___271_22189.univ_ineqs);
            implicits = (uu___271_22189.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___272_22207 = g  in
          let uu____22208 =
            let uu____22209 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____22209  in
          {
            guard_f = uu____22208;
            deferred = (uu___272_22207.deferred);
            univ_ineqs = (uu___272_22207.univ_ineqs);
            implicits = (uu___272_22207.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___273_22211 = g  in
          let uu____22212 =
            let uu____22213 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____22213  in
          {
            guard_f = uu____22212;
            deferred = (uu___273_22211.deferred);
            univ_ineqs = (uu___273_22211.univ_ineqs);
            implicits = (uu___273_22211.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____22219 ->
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
          let uu____22234 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____22234
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____22240 =
      let uu____22241 = FStar_Syntax_Util.unmeta t  in
      uu____22241.FStar_Syntax_Syntax.n  in
    match uu____22240 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____22245 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____22286 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____22286;
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
                       let uu____22376 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____22376
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___274_22380 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___274_22380.deferred);
              univ_ineqs = (uu___274_22380.univ_ineqs);
              implicits = (uu___274_22380.implicits)
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
               let uu____22413 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____22413
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
            let uu___275_22436 = g  in
            let uu____22437 =
              let uu____22438 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____22438  in
            {
              guard_f = uu____22437;
              deferred = (uu___275_22436.deferred);
              univ_ineqs = (uu___275_22436.univ_ineqs);
              implicits = (uu___275_22436.implicits)
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
            let uu____22476 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____22476 with
            | FStar_Pervasives_Native.Some
                (uu____22501::(tm,uu____22503)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____22567 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____22585 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____22585;
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
                    let uu___276_22620 = trivial_guard  in
                    {
                      guard_f = (uu___276_22620.guard_f);
                      deferred = (uu___276_22620.deferred);
                      univ_ineqs = (uu___276_22620.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____22637  -> ());
    push = (fun uu____22639  -> ());
    pop = (fun uu____22641  -> ());
    snapshot =
      (fun uu____22643  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____22652  -> fun uu____22653  -> ());
    encode_modul = (fun uu____22664  -> fun uu____22665  -> ());
    encode_sig = (fun uu____22668  -> fun uu____22669  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____22675 =
             let uu____22682 = FStar_Options.peek ()  in (e, g, uu____22682)
              in
           [uu____22675]);
    solve = (fun uu____22698  -> fun uu____22699  -> fun uu____22700  -> ());
    finish = (fun uu____22706  -> ());
    refresh = (fun uu____22708  -> ())
  } 