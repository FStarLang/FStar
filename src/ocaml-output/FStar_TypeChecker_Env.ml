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
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__normalized_eff_names
  
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
           (fun uu___225_9674  ->
              match uu___225_9674 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9677 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9677  in
                  let uu____9678 =
                    let uu____9679 = FStar_Syntax_Subst.compress y  in
                    uu____9679.FStar_Syntax_Syntax.n  in
                  (match uu____9678 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9683 =
                         let uu___239_9684 = y1  in
                         let uu____9685 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___239_9684.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___239_9684.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9685
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9683
                   | uu____9688 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___240_9700 = env  in
      let uu____9701 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___240_9700.solver);
        range = (uu___240_9700.range);
        curmodule = (uu___240_9700.curmodule);
        gamma = uu____9701;
        gamma_sig = (uu___240_9700.gamma_sig);
        gamma_cache = (uu___240_9700.gamma_cache);
        modules = (uu___240_9700.modules);
        expected_typ = (uu___240_9700.expected_typ);
        sigtab = (uu___240_9700.sigtab);
        attrtab = (uu___240_9700.attrtab);
        is_pattern = (uu___240_9700.is_pattern);
        instantiate_imp = (uu___240_9700.instantiate_imp);
        effects = (uu___240_9700.effects);
        generalize = (uu___240_9700.generalize);
        letrecs = (uu___240_9700.letrecs);
        top_level = (uu___240_9700.top_level);
        check_uvars = (uu___240_9700.check_uvars);
        use_eq = (uu___240_9700.use_eq);
        is_iface = (uu___240_9700.is_iface);
        admit = (uu___240_9700.admit);
        lax = (uu___240_9700.lax);
        lax_universes = (uu___240_9700.lax_universes);
        phase1 = (uu___240_9700.phase1);
        failhard = (uu___240_9700.failhard);
        nosynth = (uu___240_9700.nosynth);
        uvar_subtyping = (uu___240_9700.uvar_subtyping);
        tc_term = (uu___240_9700.tc_term);
        type_of = (uu___240_9700.type_of);
        universe_of = (uu___240_9700.universe_of);
        check_type_of = (uu___240_9700.check_type_of);
        use_bv_sorts = (uu___240_9700.use_bv_sorts);
        qtbl_name_and_index = (uu___240_9700.qtbl_name_and_index);
        normalized_eff_names = (uu___240_9700.normalized_eff_names);
        proof_ns = (uu___240_9700.proof_ns);
        synth_hook = (uu___240_9700.synth_hook);
        splice = (uu___240_9700.splice);
        is_native_tactic = (uu___240_9700.is_native_tactic);
        identifier_info = (uu___240_9700.identifier_info);
        tc_hooks = (uu___240_9700.tc_hooks);
        dsenv = (uu___240_9700.dsenv);
        nbe = (uu___240_9700.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9708  -> fun uu____9709  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___241_9729 = env  in
      {
        solver = (uu___241_9729.solver);
        range = (uu___241_9729.range);
        curmodule = (uu___241_9729.curmodule);
        gamma = (uu___241_9729.gamma);
        gamma_sig = (uu___241_9729.gamma_sig);
        gamma_cache = (uu___241_9729.gamma_cache);
        modules = (uu___241_9729.modules);
        expected_typ = (uu___241_9729.expected_typ);
        sigtab = (uu___241_9729.sigtab);
        attrtab = (uu___241_9729.attrtab);
        is_pattern = (uu___241_9729.is_pattern);
        instantiate_imp = (uu___241_9729.instantiate_imp);
        effects = (uu___241_9729.effects);
        generalize = (uu___241_9729.generalize);
        letrecs = (uu___241_9729.letrecs);
        top_level = (uu___241_9729.top_level);
        check_uvars = (uu___241_9729.check_uvars);
        use_eq = (uu___241_9729.use_eq);
        is_iface = (uu___241_9729.is_iface);
        admit = (uu___241_9729.admit);
        lax = (uu___241_9729.lax);
        lax_universes = (uu___241_9729.lax_universes);
        phase1 = (uu___241_9729.phase1);
        failhard = (uu___241_9729.failhard);
        nosynth = (uu___241_9729.nosynth);
        uvar_subtyping = (uu___241_9729.uvar_subtyping);
        tc_term = (uu___241_9729.tc_term);
        type_of = (uu___241_9729.type_of);
        universe_of = (uu___241_9729.universe_of);
        check_type_of = (uu___241_9729.check_type_of);
        use_bv_sorts = (uu___241_9729.use_bv_sorts);
        qtbl_name_and_index = (uu___241_9729.qtbl_name_and_index);
        normalized_eff_names = (uu___241_9729.normalized_eff_names);
        proof_ns = (uu___241_9729.proof_ns);
        synth_hook = (uu___241_9729.synth_hook);
        splice = (uu___241_9729.splice);
        is_native_tactic = (uu___241_9729.is_native_tactic);
        identifier_info = (uu___241_9729.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___241_9729.dsenv);
        nbe = (uu___241_9729.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___242_9740 = e  in
      let uu____9741 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___242_9740.solver);
        range = (uu___242_9740.range);
        curmodule = (uu___242_9740.curmodule);
        gamma = (uu___242_9740.gamma);
        gamma_sig = (uu___242_9740.gamma_sig);
        gamma_cache = (uu___242_9740.gamma_cache);
        modules = (uu___242_9740.modules);
        expected_typ = (uu___242_9740.expected_typ);
        sigtab = (uu___242_9740.sigtab);
        attrtab = (uu___242_9740.attrtab);
        is_pattern = (uu___242_9740.is_pattern);
        instantiate_imp = (uu___242_9740.instantiate_imp);
        effects = (uu___242_9740.effects);
        generalize = (uu___242_9740.generalize);
        letrecs = (uu___242_9740.letrecs);
        top_level = (uu___242_9740.top_level);
        check_uvars = (uu___242_9740.check_uvars);
        use_eq = (uu___242_9740.use_eq);
        is_iface = (uu___242_9740.is_iface);
        admit = (uu___242_9740.admit);
        lax = (uu___242_9740.lax);
        lax_universes = (uu___242_9740.lax_universes);
        phase1 = (uu___242_9740.phase1);
        failhard = (uu___242_9740.failhard);
        nosynth = (uu___242_9740.nosynth);
        uvar_subtyping = (uu___242_9740.uvar_subtyping);
        tc_term = (uu___242_9740.tc_term);
        type_of = (uu___242_9740.type_of);
        universe_of = (uu___242_9740.universe_of);
        check_type_of = (uu___242_9740.check_type_of);
        use_bv_sorts = (uu___242_9740.use_bv_sorts);
        qtbl_name_and_index = (uu___242_9740.qtbl_name_and_index);
        normalized_eff_names = (uu___242_9740.normalized_eff_names);
        proof_ns = (uu___242_9740.proof_ns);
        synth_hook = (uu___242_9740.synth_hook);
        splice = (uu___242_9740.splice);
        is_native_tactic = (uu___242_9740.is_native_tactic);
        identifier_info = (uu___242_9740.identifier_info);
        tc_hooks = (uu___242_9740.tc_hooks);
        dsenv = uu____9741;
        nbe = (uu___242_9740.nbe)
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
      | (NoDelta ,uu____9764) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____9765,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____9766,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____9767 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____9776 . unit -> 'Auu____9776 FStar_Util.smap =
  fun uu____9783  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____9788 . unit -> 'Auu____9788 FStar_Util.smap =
  fun uu____9795  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____9929 = new_gamma_cache ()  in
                  let uu____9932 = new_sigtab ()  in
                  let uu____9935 = new_sigtab ()  in
                  let uu____9942 =
                    let uu____9955 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____9955, FStar_Pervasives_Native.None)  in
                  let uu____9970 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____9973 = FStar_Options.using_facts_from ()  in
                  let uu____9974 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____9977 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____9929;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____9932;
                    attrtab = uu____9935;
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
                    qtbl_name_and_index = uu____9942;
                    normalized_eff_names = uu____9970;
                    proof_ns = uu____9973;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10013  -> false);
                    identifier_info = uu____9974;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____9977;
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
  fun uu____10122  ->
    let uu____10123 = FStar_ST.op_Bang query_indices  in
    match uu____10123 with
    | [] -> failwith "Empty query indices!"
    | uu____10173 ->
        let uu____10182 =
          let uu____10191 =
            let uu____10198 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10198  in
          let uu____10248 = FStar_ST.op_Bang query_indices  in uu____10191 ::
            uu____10248
           in
        FStar_ST.op_Colon_Equals query_indices uu____10182
  
let (pop_query_indices : unit -> unit) =
  fun uu____10337  ->
    let uu____10338 = FStar_ST.op_Bang query_indices  in
    match uu____10338 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10453  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10483  ->
    match uu____10483 with
    | (l,n1) ->
        let uu____10490 = FStar_ST.op_Bang query_indices  in
        (match uu____10490 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10601 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10620  ->
    let uu____10621 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10621
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10697 =
       let uu____10700 = FStar_ST.op_Bang stack  in env :: uu____10700  in
     FStar_ST.op_Colon_Equals stack uu____10697);
    (let uu___243_10749 = env  in
     let uu____10750 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____10753 = FStar_Util.smap_copy (sigtab env)  in
     let uu____10756 = FStar_Util.smap_copy (attrtab env)  in
     let uu____10763 =
       let uu____10776 =
         let uu____10779 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____10779  in
       let uu____10804 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____10776, uu____10804)  in
     let uu____10845 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____10848 =
       let uu____10851 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____10851  in
     {
       solver = (uu___243_10749.solver);
       range = (uu___243_10749.range);
       curmodule = (uu___243_10749.curmodule);
       gamma = (uu___243_10749.gamma);
       gamma_sig = (uu___243_10749.gamma_sig);
       gamma_cache = uu____10750;
       modules = (uu___243_10749.modules);
       expected_typ = (uu___243_10749.expected_typ);
       sigtab = uu____10753;
       attrtab = uu____10756;
       is_pattern = (uu___243_10749.is_pattern);
       instantiate_imp = (uu___243_10749.instantiate_imp);
       effects = (uu___243_10749.effects);
       generalize = (uu___243_10749.generalize);
       letrecs = (uu___243_10749.letrecs);
       top_level = (uu___243_10749.top_level);
       check_uvars = (uu___243_10749.check_uvars);
       use_eq = (uu___243_10749.use_eq);
       is_iface = (uu___243_10749.is_iface);
       admit = (uu___243_10749.admit);
       lax = (uu___243_10749.lax);
       lax_universes = (uu___243_10749.lax_universes);
       phase1 = (uu___243_10749.phase1);
       failhard = (uu___243_10749.failhard);
       nosynth = (uu___243_10749.nosynth);
       uvar_subtyping = (uu___243_10749.uvar_subtyping);
       tc_term = (uu___243_10749.tc_term);
       type_of = (uu___243_10749.type_of);
       universe_of = (uu___243_10749.universe_of);
       check_type_of = (uu___243_10749.check_type_of);
       use_bv_sorts = (uu___243_10749.use_bv_sorts);
       qtbl_name_and_index = uu____10763;
       normalized_eff_names = uu____10845;
       proof_ns = (uu___243_10749.proof_ns);
       synth_hook = (uu___243_10749.synth_hook);
       splice = (uu___243_10749.splice);
       is_native_tactic = (uu___243_10749.is_native_tactic);
       identifier_info = uu____10848;
       tc_hooks = (uu___243_10749.tc_hooks);
       dsenv = (uu___243_10749.dsenv);
       nbe = (uu___243_10749.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____10903  ->
    let uu____10904 = FStar_ST.op_Bang stack  in
    match uu____10904 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10958 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____11030  ->
           let uu____11031 = snapshot_stack env  in
           match uu____11031 with
           | (stack_depth,env1) ->
               let uu____11056 = snapshot_query_indices ()  in
               (match uu____11056 with
                | (query_indices_depth,()) ->
                    let uu____11080 = (env1.solver).snapshot msg  in
                    (match uu____11080 with
                     | (solver_depth,()) ->
                         let uu____11122 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11122 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___244_11168 = env1  in
                                 {
                                   solver = (uu___244_11168.solver);
                                   range = (uu___244_11168.range);
                                   curmodule = (uu___244_11168.curmodule);
                                   gamma = (uu___244_11168.gamma);
                                   gamma_sig = (uu___244_11168.gamma_sig);
                                   gamma_cache = (uu___244_11168.gamma_cache);
                                   modules = (uu___244_11168.modules);
                                   expected_typ =
                                     (uu___244_11168.expected_typ);
                                   sigtab = (uu___244_11168.sigtab);
                                   attrtab = (uu___244_11168.attrtab);
                                   is_pattern = (uu___244_11168.is_pattern);
                                   instantiate_imp =
                                     (uu___244_11168.instantiate_imp);
                                   effects = (uu___244_11168.effects);
                                   generalize = (uu___244_11168.generalize);
                                   letrecs = (uu___244_11168.letrecs);
                                   top_level = (uu___244_11168.top_level);
                                   check_uvars = (uu___244_11168.check_uvars);
                                   use_eq = (uu___244_11168.use_eq);
                                   is_iface = (uu___244_11168.is_iface);
                                   admit = (uu___244_11168.admit);
                                   lax = (uu___244_11168.lax);
                                   lax_universes =
                                     (uu___244_11168.lax_universes);
                                   phase1 = (uu___244_11168.phase1);
                                   failhard = (uu___244_11168.failhard);
                                   nosynth = (uu___244_11168.nosynth);
                                   uvar_subtyping =
                                     (uu___244_11168.uvar_subtyping);
                                   tc_term = (uu___244_11168.tc_term);
                                   type_of = (uu___244_11168.type_of);
                                   universe_of = (uu___244_11168.universe_of);
                                   check_type_of =
                                     (uu___244_11168.check_type_of);
                                   use_bv_sorts =
                                     (uu___244_11168.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___244_11168.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___244_11168.normalized_eff_names);
                                   proof_ns = (uu___244_11168.proof_ns);
                                   synth_hook = (uu___244_11168.synth_hook);
                                   splice = (uu___244_11168.splice);
                                   is_native_tactic =
                                     (uu___244_11168.is_native_tactic);
                                   identifier_info =
                                     (uu___244_11168.identifier_info);
                                   tc_hooks = (uu___244_11168.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___244_11168.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11199  ->
             let uu____11200 =
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
             match uu____11200 with
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
                             ((let uu____11326 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11326
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11337 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11337
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11364,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11396 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11422  ->
                  match uu____11422 with
                  | (m,uu____11428) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11396 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___245_11436 = env  in
               {
                 solver = (uu___245_11436.solver);
                 range = (uu___245_11436.range);
                 curmodule = (uu___245_11436.curmodule);
                 gamma = (uu___245_11436.gamma);
                 gamma_sig = (uu___245_11436.gamma_sig);
                 gamma_cache = (uu___245_11436.gamma_cache);
                 modules = (uu___245_11436.modules);
                 expected_typ = (uu___245_11436.expected_typ);
                 sigtab = (uu___245_11436.sigtab);
                 attrtab = (uu___245_11436.attrtab);
                 is_pattern = (uu___245_11436.is_pattern);
                 instantiate_imp = (uu___245_11436.instantiate_imp);
                 effects = (uu___245_11436.effects);
                 generalize = (uu___245_11436.generalize);
                 letrecs = (uu___245_11436.letrecs);
                 top_level = (uu___245_11436.top_level);
                 check_uvars = (uu___245_11436.check_uvars);
                 use_eq = (uu___245_11436.use_eq);
                 is_iface = (uu___245_11436.is_iface);
                 admit = (uu___245_11436.admit);
                 lax = (uu___245_11436.lax);
                 lax_universes = (uu___245_11436.lax_universes);
                 phase1 = (uu___245_11436.phase1);
                 failhard = (uu___245_11436.failhard);
                 nosynth = (uu___245_11436.nosynth);
                 uvar_subtyping = (uu___245_11436.uvar_subtyping);
                 tc_term = (uu___245_11436.tc_term);
                 type_of = (uu___245_11436.type_of);
                 universe_of = (uu___245_11436.universe_of);
                 check_type_of = (uu___245_11436.check_type_of);
                 use_bv_sorts = (uu___245_11436.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___245_11436.normalized_eff_names);
                 proof_ns = (uu___245_11436.proof_ns);
                 synth_hook = (uu___245_11436.synth_hook);
                 splice = (uu___245_11436.splice);
                 is_native_tactic = (uu___245_11436.is_native_tactic);
                 identifier_info = (uu___245_11436.identifier_info);
                 tc_hooks = (uu___245_11436.tc_hooks);
                 dsenv = (uu___245_11436.dsenv);
                 nbe = (uu___245_11436.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11449,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___246_11458 = env  in
               {
                 solver = (uu___246_11458.solver);
                 range = (uu___246_11458.range);
                 curmodule = (uu___246_11458.curmodule);
                 gamma = (uu___246_11458.gamma);
                 gamma_sig = (uu___246_11458.gamma_sig);
                 gamma_cache = (uu___246_11458.gamma_cache);
                 modules = (uu___246_11458.modules);
                 expected_typ = (uu___246_11458.expected_typ);
                 sigtab = (uu___246_11458.sigtab);
                 attrtab = (uu___246_11458.attrtab);
                 is_pattern = (uu___246_11458.is_pattern);
                 instantiate_imp = (uu___246_11458.instantiate_imp);
                 effects = (uu___246_11458.effects);
                 generalize = (uu___246_11458.generalize);
                 letrecs = (uu___246_11458.letrecs);
                 top_level = (uu___246_11458.top_level);
                 check_uvars = (uu___246_11458.check_uvars);
                 use_eq = (uu___246_11458.use_eq);
                 is_iface = (uu___246_11458.is_iface);
                 admit = (uu___246_11458.admit);
                 lax = (uu___246_11458.lax);
                 lax_universes = (uu___246_11458.lax_universes);
                 phase1 = (uu___246_11458.phase1);
                 failhard = (uu___246_11458.failhard);
                 nosynth = (uu___246_11458.nosynth);
                 uvar_subtyping = (uu___246_11458.uvar_subtyping);
                 tc_term = (uu___246_11458.tc_term);
                 type_of = (uu___246_11458.type_of);
                 universe_of = (uu___246_11458.universe_of);
                 check_type_of = (uu___246_11458.check_type_of);
                 use_bv_sorts = (uu___246_11458.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___246_11458.normalized_eff_names);
                 proof_ns = (uu___246_11458.proof_ns);
                 synth_hook = (uu___246_11458.synth_hook);
                 splice = (uu___246_11458.splice);
                 is_native_tactic = (uu___246_11458.is_native_tactic);
                 identifier_info = (uu___246_11458.identifier_info);
                 tc_hooks = (uu___246_11458.tc_hooks);
                 dsenv = (uu___246_11458.dsenv);
                 nbe = (uu___246_11458.nbe)
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
        (let uu___247_11492 = e  in
         {
           solver = (uu___247_11492.solver);
           range = r;
           curmodule = (uu___247_11492.curmodule);
           gamma = (uu___247_11492.gamma);
           gamma_sig = (uu___247_11492.gamma_sig);
           gamma_cache = (uu___247_11492.gamma_cache);
           modules = (uu___247_11492.modules);
           expected_typ = (uu___247_11492.expected_typ);
           sigtab = (uu___247_11492.sigtab);
           attrtab = (uu___247_11492.attrtab);
           is_pattern = (uu___247_11492.is_pattern);
           instantiate_imp = (uu___247_11492.instantiate_imp);
           effects = (uu___247_11492.effects);
           generalize = (uu___247_11492.generalize);
           letrecs = (uu___247_11492.letrecs);
           top_level = (uu___247_11492.top_level);
           check_uvars = (uu___247_11492.check_uvars);
           use_eq = (uu___247_11492.use_eq);
           is_iface = (uu___247_11492.is_iface);
           admit = (uu___247_11492.admit);
           lax = (uu___247_11492.lax);
           lax_universes = (uu___247_11492.lax_universes);
           phase1 = (uu___247_11492.phase1);
           failhard = (uu___247_11492.failhard);
           nosynth = (uu___247_11492.nosynth);
           uvar_subtyping = (uu___247_11492.uvar_subtyping);
           tc_term = (uu___247_11492.tc_term);
           type_of = (uu___247_11492.type_of);
           universe_of = (uu___247_11492.universe_of);
           check_type_of = (uu___247_11492.check_type_of);
           use_bv_sorts = (uu___247_11492.use_bv_sorts);
           qtbl_name_and_index = (uu___247_11492.qtbl_name_and_index);
           normalized_eff_names = (uu___247_11492.normalized_eff_names);
           proof_ns = (uu___247_11492.proof_ns);
           synth_hook = (uu___247_11492.synth_hook);
           splice = (uu___247_11492.splice);
           is_native_tactic = (uu___247_11492.is_native_tactic);
           identifier_info = (uu___247_11492.identifier_info);
           tc_hooks = (uu___247_11492.tc_hooks);
           dsenv = (uu___247_11492.dsenv);
           nbe = (uu___247_11492.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11508 =
        let uu____11509 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11509 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11508
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11563 =
          let uu____11564 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11564 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11563
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11618 =
          let uu____11619 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11619 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11618
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11673 =
        let uu____11674 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11674 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11673
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___248_11735 = env  in
      {
        solver = (uu___248_11735.solver);
        range = (uu___248_11735.range);
        curmodule = lid;
        gamma = (uu___248_11735.gamma);
        gamma_sig = (uu___248_11735.gamma_sig);
        gamma_cache = (uu___248_11735.gamma_cache);
        modules = (uu___248_11735.modules);
        expected_typ = (uu___248_11735.expected_typ);
        sigtab = (uu___248_11735.sigtab);
        attrtab = (uu___248_11735.attrtab);
        is_pattern = (uu___248_11735.is_pattern);
        instantiate_imp = (uu___248_11735.instantiate_imp);
        effects = (uu___248_11735.effects);
        generalize = (uu___248_11735.generalize);
        letrecs = (uu___248_11735.letrecs);
        top_level = (uu___248_11735.top_level);
        check_uvars = (uu___248_11735.check_uvars);
        use_eq = (uu___248_11735.use_eq);
        is_iface = (uu___248_11735.is_iface);
        admit = (uu___248_11735.admit);
        lax = (uu___248_11735.lax);
        lax_universes = (uu___248_11735.lax_universes);
        phase1 = (uu___248_11735.phase1);
        failhard = (uu___248_11735.failhard);
        nosynth = (uu___248_11735.nosynth);
        uvar_subtyping = (uu___248_11735.uvar_subtyping);
        tc_term = (uu___248_11735.tc_term);
        type_of = (uu___248_11735.type_of);
        universe_of = (uu___248_11735.universe_of);
        check_type_of = (uu___248_11735.check_type_of);
        use_bv_sorts = (uu___248_11735.use_bv_sorts);
        qtbl_name_and_index = (uu___248_11735.qtbl_name_and_index);
        normalized_eff_names = (uu___248_11735.normalized_eff_names);
        proof_ns = (uu___248_11735.proof_ns);
        synth_hook = (uu___248_11735.synth_hook);
        splice = (uu___248_11735.splice);
        is_native_tactic = (uu___248_11735.is_native_tactic);
        identifier_info = (uu___248_11735.identifier_info);
        tc_hooks = (uu___248_11735.tc_hooks);
        dsenv = (uu___248_11735.dsenv);
        nbe = (uu___248_11735.nbe)
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
      let uu____11762 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11762
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11772 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11772)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11782 =
      let uu____11783 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11783  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11782)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11788  ->
    let uu____11789 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11789
  
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
      | ((formals,t),uu____11883) ->
          let vs = mk_univ_subst formals us  in
          let uu____11907 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11907)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___226_11923  ->
    match uu___226_11923 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11949  -> new_u_univ ()))
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
      let uu____11968 = inst_tscheme t  in
      match uu____11968 with
      | (us,t1) ->
          let uu____11979 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11979)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11999  ->
          match uu____11999 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12020 =
                         let uu____12021 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12022 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12023 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12024 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12021 uu____12022 uu____12023 uu____12024
                          in
                       failwith uu____12020)
                    else ();
                    (let uu____12026 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12026))
               | uu____12035 ->
                   let uu____12036 =
                     let uu____12037 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12037
                      in
                   failwith uu____12036)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12043 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12049 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12055 -> false
  
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
             | ([],uu____12097) -> Maybe
             | (uu____12104,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12123 -> No  in
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
          let uu____12214 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12214 with
          | FStar_Pervasives_Native.None  ->
              let uu____12237 =
                FStar_Util.find_map env.gamma
                  (fun uu___227_12281  ->
                     match uu___227_12281 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12320 = FStar_Ident.lid_equals lid l  in
                         if uu____12320
                         then
                           let uu____12341 =
                             let uu____12360 =
                               let uu____12375 = inst_tscheme t  in
                               FStar_Util.Inl uu____12375  in
                             let uu____12390 = FStar_Ident.range_of_lid l  in
                             (uu____12360, uu____12390)  in
                           FStar_Pervasives_Native.Some uu____12341
                         else FStar_Pervasives_Native.None
                     | uu____12442 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12237
                (fun uu____12480  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___228_12489  ->
                        match uu___228_12489 with
                        | (uu____12492,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12494);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12495;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12496;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12497;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12498;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12518 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12518
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
                                  uu____12566 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12573 -> cache t  in
                            let uu____12574 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12574 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12580 =
                                   let uu____12581 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12581)
                                    in
                                 maybe_cache uu____12580)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12649 = find_in_sigtab env lid  in
         match uu____12649 with
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
      let uu____12729 = lookup_qname env lid  in
      match uu____12729 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12750,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____12861 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____12861 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____12903 =
          let uu____12906 = lookup_attr env1 attr  in se1 :: uu____12906  in
        FStar_Util.smap_add (attrtab env1) attr uu____12903  in
      FStar_List.iter
        (fun attr  ->
           let uu____12916 =
             let uu____12917 = FStar_Syntax_Subst.compress attr  in
             uu____12917.FStar_Syntax_Syntax.n  in
           match uu____12916 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____12921 =
                 let uu____12922 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____12922.FStar_Ident.str  in
               add_one1 env se uu____12921
           | uu____12923 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12945) ->
          add_sigelts env ses
      | uu____12954 ->
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
            | uu____12969 -> ()))

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
        (fun uu___229_13000  ->
           match uu___229_13000 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13018 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13079,lb::[]),uu____13081) ->
            let uu____13088 =
              let uu____13097 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13106 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13097, uu____13106)  in
            FStar_Pervasives_Native.Some uu____13088
        | FStar_Syntax_Syntax.Sig_let ((uu____13119,lbs),uu____13121) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13151 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13163 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13163
                     then
                       let uu____13174 =
                         let uu____13183 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13192 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13183, uu____13192)  in
                       FStar_Pervasives_Native.Some uu____13174
                     else FStar_Pervasives_Native.None)
        | uu____13214 -> FStar_Pervasives_Native.None
  
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
          let uu____13273 =
            let uu____13282 =
              let uu____13287 =
                let uu____13288 =
                  let uu____13291 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13291
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13288)  in
              inst_tscheme1 uu____13287  in
            (uu____13282, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13273
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13313,uu____13314) ->
          let uu____13319 =
            let uu____13328 =
              let uu____13333 =
                let uu____13334 =
                  let uu____13337 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13337  in
                (us, uu____13334)  in
              inst_tscheme1 uu____13333  in
            (uu____13328, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13319
      | uu____13356 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13444 =
          match uu____13444 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13540,uvs,t,uu____13543,uu____13544,uu____13545);
                      FStar_Syntax_Syntax.sigrng = uu____13546;
                      FStar_Syntax_Syntax.sigquals = uu____13547;
                      FStar_Syntax_Syntax.sigmeta = uu____13548;
                      FStar_Syntax_Syntax.sigattrs = uu____13549;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13570 =
                     let uu____13579 = inst_tscheme1 (uvs, t)  in
                     (uu____13579, rng)  in
                   FStar_Pervasives_Native.Some uu____13570
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13603;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13605;
                      FStar_Syntax_Syntax.sigattrs = uu____13606;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13623 =
                     let uu____13624 = in_cur_mod env l  in uu____13624 = Yes
                      in
                   if uu____13623
                   then
                     let uu____13635 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13635
                      then
                        let uu____13648 =
                          let uu____13657 = inst_tscheme1 (uvs, t)  in
                          (uu____13657, rng)  in
                        FStar_Pervasives_Native.Some uu____13648
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13688 =
                        let uu____13697 = inst_tscheme1 (uvs, t)  in
                        (uu____13697, rng)  in
                      FStar_Pervasives_Native.Some uu____13688)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13722,uu____13723);
                      FStar_Syntax_Syntax.sigrng = uu____13724;
                      FStar_Syntax_Syntax.sigquals = uu____13725;
                      FStar_Syntax_Syntax.sigmeta = uu____13726;
                      FStar_Syntax_Syntax.sigattrs = uu____13727;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13768 =
                          let uu____13777 = inst_tscheme1 (uvs, k)  in
                          (uu____13777, rng)  in
                        FStar_Pervasives_Native.Some uu____13768
                    | uu____13798 ->
                        let uu____13799 =
                          let uu____13808 =
                            let uu____13813 =
                              let uu____13814 =
                                let uu____13817 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13817
                                 in
                              (uvs, uu____13814)  in
                            inst_tscheme1 uu____13813  in
                          (uu____13808, rng)  in
                        FStar_Pervasives_Native.Some uu____13799)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13840,uu____13841);
                      FStar_Syntax_Syntax.sigrng = uu____13842;
                      FStar_Syntax_Syntax.sigquals = uu____13843;
                      FStar_Syntax_Syntax.sigmeta = uu____13844;
                      FStar_Syntax_Syntax.sigattrs = uu____13845;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13887 =
                          let uu____13896 = inst_tscheme_with (uvs, k) us  in
                          (uu____13896, rng)  in
                        FStar_Pervasives_Native.Some uu____13887
                    | uu____13917 ->
                        let uu____13918 =
                          let uu____13927 =
                            let uu____13932 =
                              let uu____13933 =
                                let uu____13936 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13936
                                 in
                              (uvs, uu____13933)  in
                            inst_tscheme_with uu____13932 us  in
                          (uu____13927, rng)  in
                        FStar_Pervasives_Native.Some uu____13918)
               | FStar_Util.Inr se ->
                   let uu____13972 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13993;
                          FStar_Syntax_Syntax.sigrng = uu____13994;
                          FStar_Syntax_Syntax.sigquals = uu____13995;
                          FStar_Syntax_Syntax.sigmeta = uu____13996;
                          FStar_Syntax_Syntax.sigattrs = uu____13997;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14012 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____13972
                     (FStar_Util.map_option
                        (fun uu____14060  ->
                           match uu____14060 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14091 =
          let uu____14102 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14102 mapper  in
        match uu____14091 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14176 =
              let uu____14187 =
                let uu____14194 =
                  let uu___249_14197 = t  in
                  let uu____14198 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___249_14197.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14198;
                    FStar_Syntax_Syntax.vars =
                      (uu___249_14197.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14194)  in
              (uu____14187, r)  in
            FStar_Pervasives_Native.Some uu____14176
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14245 = lookup_qname env l  in
      match uu____14245 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14264 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14316 = try_lookup_bv env bv  in
      match uu____14316 with
      | FStar_Pervasives_Native.None  ->
          let uu____14331 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14331 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14346 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14347 =
            let uu____14348 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14348  in
          (uu____14346, uu____14347)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14369 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14369 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14435 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14435  in
          let uu____14436 =
            let uu____14445 =
              let uu____14450 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14450)  in
            (uu____14445, r1)  in
          FStar_Pervasives_Native.Some uu____14436
  
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
        let uu____14484 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14484 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14517,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14542 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14542  in
            let uu____14543 =
              let uu____14548 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14548, r1)  in
            FStar_Pervasives_Native.Some uu____14543
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14571 = try_lookup_lid env l  in
      match uu____14571 with
      | FStar_Pervasives_Native.None  ->
          let uu____14598 = name_not_found l  in
          let uu____14603 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14598 uu____14603
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___230_14643  ->
              match uu___230_14643 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14645 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14664 = lookup_qname env lid  in
      match uu____14664 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14673,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14676;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14678;
              FStar_Syntax_Syntax.sigattrs = uu____14679;_},FStar_Pervasives_Native.None
            ),uu____14680)
          ->
          let uu____14729 =
            let uu____14736 =
              let uu____14737 =
                let uu____14740 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14740 t  in
              (uvs, uu____14737)  in
            (uu____14736, q)  in
          FStar_Pervasives_Native.Some uu____14729
      | uu____14753 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14774 = lookup_qname env lid  in
      match uu____14774 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14779,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14782;
              FStar_Syntax_Syntax.sigquals = uu____14783;
              FStar_Syntax_Syntax.sigmeta = uu____14784;
              FStar_Syntax_Syntax.sigattrs = uu____14785;_},FStar_Pervasives_Native.None
            ),uu____14786)
          ->
          let uu____14835 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14835 (uvs, t)
      | uu____14840 ->
          let uu____14841 = name_not_found lid  in
          let uu____14846 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14841 uu____14846
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14865 = lookup_qname env lid  in
      match uu____14865 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14870,uvs,t,uu____14873,uu____14874,uu____14875);
              FStar_Syntax_Syntax.sigrng = uu____14876;
              FStar_Syntax_Syntax.sigquals = uu____14877;
              FStar_Syntax_Syntax.sigmeta = uu____14878;
              FStar_Syntax_Syntax.sigattrs = uu____14879;_},FStar_Pervasives_Native.None
            ),uu____14880)
          ->
          let uu____14933 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14933 (uvs, t)
      | uu____14938 ->
          let uu____14939 = name_not_found lid  in
          let uu____14944 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14939 uu____14944
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14965 = lookup_qname env lid  in
      match uu____14965 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14972,uu____14973,uu____14974,uu____14975,uu____14976,dcs);
              FStar_Syntax_Syntax.sigrng = uu____14978;
              FStar_Syntax_Syntax.sigquals = uu____14979;
              FStar_Syntax_Syntax.sigmeta = uu____14980;
              FStar_Syntax_Syntax.sigattrs = uu____14981;_},uu____14982),uu____14983)
          -> (true, dcs)
      | uu____15044 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15057 = lookup_qname env lid  in
      match uu____15057 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15058,uu____15059,uu____15060,l,uu____15062,uu____15063);
              FStar_Syntax_Syntax.sigrng = uu____15064;
              FStar_Syntax_Syntax.sigquals = uu____15065;
              FStar_Syntax_Syntax.sigmeta = uu____15066;
              FStar_Syntax_Syntax.sigattrs = uu____15067;_},uu____15068),uu____15069)
          -> l
      | uu____15124 ->
          let uu____15125 =
            let uu____15126 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15126  in
          failwith uu____15125
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15175)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15226,lbs),uu____15228)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15250 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15250
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15282 -> FStar_Pervasives_Native.None)
        | uu____15287 -> FStar_Pervasives_Native.None
  
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
        let uu____15317 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15317
  
let (delta_depth_of_qninfo :
  FStar_Ident.lident ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun lid  ->
    fun qn  ->
      match qn with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15356,uu____15357)
          -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____15405),uu____15406) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____15455 ->
               FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.parse_int "0"))
           | FStar_Syntax_Syntax.Sig_bundle uu____15472 ->
               FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.parse_int "0"))
           | FStar_Syntax_Syntax.Sig_datacon uu____15481 ->
               FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.parse_int "0"))
           | FStar_Syntax_Syntax.Sig_declare_typ uu____15496 ->
               FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_abstract
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "0")))
           | FStar_Syntax_Syntax.Sig_let ((uu____15503,lbs),uu____15505) ->
               FStar_Util.find_map lbs
                 (fun lb  ->
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                       in
                    let uu____15519 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                       in
                    if uu____15519
                    then
                      FStar_Pervasives_Native.Some
                        (fv.FStar_Syntax_Syntax.fv_delta)
                    else FStar_Pervasives_Native.None)
           | FStar_Syntax_Syntax.Sig_main uu____15523 ->
               FStar_Pervasives_Native.None
           | FStar_Syntax_Syntax.Sig_assume uu____15524 ->
               FStar_Pervasives_Native.None
           | FStar_Syntax_Syntax.Sig_new_effect uu____15531 ->
               FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.parse_int "0"))
           | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15532 ->
               FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.parse_int "0"))
           | FStar_Syntax_Syntax.Sig_sub_effect uu____15533 ->
               FStar_Pervasives_Native.None
           | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15534 ->
               FStar_Pervasives_Native.None
           | FStar_Syntax_Syntax.Sig_pragma uu____15547 ->
               FStar_Pervasives_Native.None
           | FStar_Syntax_Syntax.Sig_splice uu____15548 ->
               FStar_Pervasives_Native.None)
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let uu____15565 =
        let uu____15568 =
          lookup_qname env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        delta_depth_of_qninfo
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____15568
         in
      match uu____15565 with
      | FStar_Pervasives_Native.None  ->
          let uu____15569 =
            let uu____15570 = FStar_Syntax_Print.fv_to_string fv  in
            FStar_Util.format1 "Delta depth not found for %s" uu____15570  in
          failwith uu____15569
      | FStar_Pervasives_Native.Some d -> d
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15590),uu____15591) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15640 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15661),uu____15662) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15711 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15732 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15732
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15751 = lookup_qname env ftv  in
      match uu____15751 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15755) ->
          let uu____15800 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15800 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15821,t),r) ->
               let uu____15836 =
                 let uu____15837 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15837 t  in
               FStar_Pervasives_Native.Some uu____15836)
      | uu____15838 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15849 = try_lookup_effect_lid env ftv  in
      match uu____15849 with
      | FStar_Pervasives_Native.None  ->
          let uu____15852 = name_not_found ftv  in
          let uu____15857 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15852 uu____15857
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
        let uu____15880 = lookup_qname env lid0  in
        match uu____15880 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15891);
                FStar_Syntax_Syntax.sigrng = uu____15892;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15894;
                FStar_Syntax_Syntax.sigattrs = uu____15895;_},FStar_Pervasives_Native.None
              ),uu____15896)
            ->
            let lid1 =
              let uu____15950 =
                let uu____15951 = FStar_Ident.range_of_lid lid  in
                let uu____15952 =
                  let uu____15953 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____15953  in
                FStar_Range.set_use_range uu____15951 uu____15952  in
              FStar_Ident.set_lid_range lid uu____15950  in
            let uu____15954 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___231_15958  ->
                      match uu___231_15958 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____15959 -> false))
               in
            if uu____15954
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15973 =
                      let uu____15974 =
                        let uu____15975 = get_range env  in
                        FStar_Range.string_of_range uu____15975  in
                      let uu____15976 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____15977 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15974 uu____15976 uu____15977
                       in
                    failwith uu____15973)
                  in
               match (binders, univs1) with
               | ([],uu____15994) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16019,uu____16020::uu____16021::uu____16022) ->
                   let uu____16043 =
                     let uu____16044 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____16045 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16044 uu____16045
                      in
                   failwith uu____16043
               | uu____16052 ->
                   let uu____16067 =
                     let uu____16072 =
                       let uu____16073 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____16073)  in
                     inst_tscheme_with uu____16072 insts  in
                   (match uu____16067 with
                    | (uu____16086,t) ->
                        let t1 =
                          let uu____16089 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16089 t  in
                        let uu____16090 =
                          let uu____16091 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16091.FStar_Syntax_Syntax.n  in
                        (match uu____16090 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16126 -> failwith "Impossible")))
        | uu____16133 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16156 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16156 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16169,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16176 = find1 l2  in
            (match uu____16176 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16183 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16183 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16187 = find1 l  in
            (match uu____16187 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16192 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16192
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16206 = lookup_qname env l1  in
      match uu____16206 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16209;
              FStar_Syntax_Syntax.sigrng = uu____16210;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16212;
              FStar_Syntax_Syntax.sigattrs = uu____16213;_},uu____16214),uu____16215)
          -> q
      | uu____16266 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16287 =
          let uu____16288 =
            let uu____16289 = FStar_Util.string_of_int i  in
            let uu____16290 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16289 uu____16290
             in
          failwith uu____16288  in
        let uu____16291 = lookup_datacon env lid  in
        match uu____16291 with
        | (uu____16296,t) ->
            let uu____16298 =
              let uu____16299 = FStar_Syntax_Subst.compress t  in
              uu____16299.FStar_Syntax_Syntax.n  in
            (match uu____16298 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16303) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16344 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16344
                      FStar_Pervasives_Native.fst)
             | uu____16355 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16366 = lookup_qname env l  in
      match uu____16366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16367,uu____16368,uu____16369);
              FStar_Syntax_Syntax.sigrng = uu____16370;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16372;
              FStar_Syntax_Syntax.sigattrs = uu____16373;_},uu____16374),uu____16375)
          ->
          FStar_Util.for_some
            (fun uu___232_16428  ->
               match uu___232_16428 with
               | FStar_Syntax_Syntax.Projector uu____16429 -> true
               | uu____16434 -> false) quals
      | uu____16435 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16446 = lookup_qname env lid  in
      match uu____16446 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16447,uu____16448,uu____16449,uu____16450,uu____16451,uu____16452);
              FStar_Syntax_Syntax.sigrng = uu____16453;
              FStar_Syntax_Syntax.sigquals = uu____16454;
              FStar_Syntax_Syntax.sigmeta = uu____16455;
              FStar_Syntax_Syntax.sigattrs = uu____16456;_},uu____16457),uu____16458)
          -> true
      | uu____16513 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16524 = lookup_qname env lid  in
      match uu____16524 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16525,uu____16526,uu____16527,uu____16528,uu____16529,uu____16530);
              FStar_Syntax_Syntax.sigrng = uu____16531;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16533;
              FStar_Syntax_Syntax.sigattrs = uu____16534;_},uu____16535),uu____16536)
          ->
          FStar_Util.for_some
            (fun uu___233_16597  ->
               match uu___233_16597 with
               | FStar_Syntax_Syntax.RecordType uu____16598 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16607 -> true
               | uu____16616 -> false) quals
      | uu____16617 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16623,uu____16624);
            FStar_Syntax_Syntax.sigrng = uu____16625;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16627;
            FStar_Syntax_Syntax.sigattrs = uu____16628;_},uu____16629),uu____16630)
        ->
        FStar_Util.for_some
          (fun uu___234_16687  ->
             match uu___234_16687 with
             | FStar_Syntax_Syntax.Action uu____16688 -> true
             | uu____16689 -> false) quals
    | uu____16690 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16701 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16701
  
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
      let uu____16715 =
        let uu____16716 = FStar_Syntax_Util.un_uinst head1  in
        uu____16716.FStar_Syntax_Syntax.n  in
      match uu____16715 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16720 ->
               true
           | uu____16721 -> false)
      | uu____16722 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16733 = lookup_qname env l  in
      match uu____16733 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16735),uu____16736) ->
          FStar_Util.for_some
            (fun uu___235_16784  ->
               match uu___235_16784 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16785 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16786 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16857 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16873) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16890 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16897 ->
                 FStar_Pervasives_Native.Some true
             | uu____16914 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16915 =
        let uu____16918 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16918 mapper  in
      match uu____16915 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____16970 = lookup_qname env lid  in
      match uu____16970 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16973,uu____16974,tps,uu____16976,uu____16977,uu____16978);
              FStar_Syntax_Syntax.sigrng = uu____16979;
              FStar_Syntax_Syntax.sigquals = uu____16980;
              FStar_Syntax_Syntax.sigmeta = uu____16981;
              FStar_Syntax_Syntax.sigattrs = uu____16982;_},uu____16983),uu____16984)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____17049 -> FStar_Pervasives_Native.None
  
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
           (fun uu____17093  ->
              match uu____17093 with
              | (d,uu____17101) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17116 = effect_decl_opt env l  in
      match uu____17116 with
      | FStar_Pervasives_Native.None  ->
          let uu____17131 = name_not_found l  in
          let uu____17136 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17131 uu____17136
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17158  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17177  ->
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
        let uu____17208 = FStar_Ident.lid_equals l1 l2  in
        if uu____17208
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17216 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17216
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17224 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17277  ->
                        match uu____17277 with
                        | (m1,m2,uu____17290,uu____17291,uu____17292) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17224 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17309 =
                    let uu____17314 =
                      let uu____17315 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17316 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17315
                        uu____17316
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17314)
                     in
                  FStar_Errors.raise_error uu____17309 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17323,uu____17324,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17357 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17357
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
  'Auu____17373 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17373)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17402 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17428  ->
                match uu____17428 with
                | (d,uu____17434) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17402 with
      | FStar_Pervasives_Native.None  ->
          let uu____17445 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17445
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17458 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17458 with
           | (uu____17473,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17491)::(wp,uu____17493)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17549 -> failwith "Impossible"))
  
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
          let uu____17604 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17604
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17606 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17606
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
                  let uu____17614 = get_range env  in
                  let uu____17615 =
                    let uu____17622 =
                      let uu____17623 =
                        let uu____17640 =
                          let uu____17651 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17651]  in
                        (null_wp, uu____17640)  in
                      FStar_Syntax_Syntax.Tm_app uu____17623  in
                    FStar_Syntax_Syntax.mk uu____17622  in
                  uu____17615 FStar_Pervasives_Native.None uu____17614  in
                let uu____17691 =
                  let uu____17692 =
                    let uu____17703 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17703]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17692;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17691))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___250_17740 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___250_17740.order);
              joins = (uu___250_17740.joins)
            }  in
          let uu___251_17749 = env  in
          {
            solver = (uu___251_17749.solver);
            range = (uu___251_17749.range);
            curmodule = (uu___251_17749.curmodule);
            gamma = (uu___251_17749.gamma);
            gamma_sig = (uu___251_17749.gamma_sig);
            gamma_cache = (uu___251_17749.gamma_cache);
            modules = (uu___251_17749.modules);
            expected_typ = (uu___251_17749.expected_typ);
            sigtab = (uu___251_17749.sigtab);
            attrtab = (uu___251_17749.attrtab);
            is_pattern = (uu___251_17749.is_pattern);
            instantiate_imp = (uu___251_17749.instantiate_imp);
            effects;
            generalize = (uu___251_17749.generalize);
            letrecs = (uu___251_17749.letrecs);
            top_level = (uu___251_17749.top_level);
            check_uvars = (uu___251_17749.check_uvars);
            use_eq = (uu___251_17749.use_eq);
            is_iface = (uu___251_17749.is_iface);
            admit = (uu___251_17749.admit);
            lax = (uu___251_17749.lax);
            lax_universes = (uu___251_17749.lax_universes);
            phase1 = (uu___251_17749.phase1);
            failhard = (uu___251_17749.failhard);
            nosynth = (uu___251_17749.nosynth);
            uvar_subtyping = (uu___251_17749.uvar_subtyping);
            tc_term = (uu___251_17749.tc_term);
            type_of = (uu___251_17749.type_of);
            universe_of = (uu___251_17749.universe_of);
            check_type_of = (uu___251_17749.check_type_of);
            use_bv_sorts = (uu___251_17749.use_bv_sorts);
            qtbl_name_and_index = (uu___251_17749.qtbl_name_and_index);
            normalized_eff_names = (uu___251_17749.normalized_eff_names);
            proof_ns = (uu___251_17749.proof_ns);
            synth_hook = (uu___251_17749.synth_hook);
            splice = (uu___251_17749.splice);
            is_native_tactic = (uu___251_17749.is_native_tactic);
            identifier_info = (uu___251_17749.identifier_info);
            tc_hooks = (uu___251_17749.tc_hooks);
            dsenv = (uu___251_17749.dsenv);
            nbe = (uu___251_17749.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17779 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17779  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____17937 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____17938 = l1 u t wp e  in
                                l2 u t uu____17937 uu____17938))
                | uu____17939 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____18011 = inst_tscheme_with lift_t [u]  in
            match uu____18011 with
            | (uu____18018,lift_t1) ->
                let uu____18020 =
                  let uu____18027 =
                    let uu____18028 =
                      let uu____18045 =
                        let uu____18056 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18065 =
                          let uu____18076 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18076]  in
                        uu____18056 :: uu____18065  in
                      (lift_t1, uu____18045)  in
                    FStar_Syntax_Syntax.Tm_app uu____18028  in
                  FStar_Syntax_Syntax.mk uu____18027  in
                uu____18020 FStar_Pervasives_Native.None
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
            let uu____18188 = inst_tscheme_with lift_t [u]  in
            match uu____18188 with
            | (uu____18195,lift_t1) ->
                let uu____18197 =
                  let uu____18204 =
                    let uu____18205 =
                      let uu____18222 =
                        let uu____18233 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18242 =
                          let uu____18253 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18262 =
                            let uu____18273 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18273]  in
                          uu____18253 :: uu____18262  in
                        uu____18233 :: uu____18242  in
                      (lift_t1, uu____18222)  in
                    FStar_Syntax_Syntax.Tm_app uu____18205  in
                  FStar_Syntax_Syntax.mk uu____18204  in
                uu____18197 FStar_Pervasives_Native.None
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
              let uu____18375 =
                let uu____18376 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18376
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18375  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18380 =
              let uu____18381 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18381  in
            let uu____18382 =
              let uu____18383 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18409 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18409)
                 in
              FStar_Util.dflt "none" uu____18383  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18380
              uu____18382
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18435  ->
                    match uu____18435 with
                    | (e,uu____18443) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18466 =
            match uu____18466 with
            | (i,j) ->
                let uu____18477 = FStar_Ident.lid_equals i j  in
                if uu____18477
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
              let uu____18509 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18519 = FStar_Ident.lid_equals i k  in
                        if uu____18519
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18530 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18530
                                  then []
                                  else
                                    (let uu____18534 =
                                       let uu____18543 =
                                         find_edge order1 (i, k)  in
                                       let uu____18546 =
                                         find_edge order1 (k, j)  in
                                       (uu____18543, uu____18546)  in
                                     match uu____18534 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18561 =
                                           compose_edges e1 e2  in
                                         [uu____18561]
                                     | uu____18562 -> [])))))
                 in
              FStar_List.append order1 uu____18509  in
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
                   let uu____18592 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18594 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18594
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18592
                   then
                     let uu____18599 =
                       let uu____18604 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18604)
                        in
                     let uu____18605 = get_range env  in
                     FStar_Errors.raise_error uu____18599 uu____18605
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18682 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18682
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18731 =
                                              let uu____18740 =
                                                find_edge order2 (i, k)  in
                                              let uu____18743 =
                                                find_edge order2 (j, k)  in
                                              (uu____18740, uu____18743)  in
                                            match uu____18731 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18785,uu____18786)
                                                     ->
                                                     let uu____18793 =
                                                       let uu____18798 =
                                                         let uu____18799 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18799
                                                          in
                                                       let uu____18802 =
                                                         let uu____18803 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18803
                                                          in
                                                       (uu____18798,
                                                         uu____18802)
                                                        in
                                                     (match uu____18793 with
                                                      | (true ,true ) ->
                                                          let uu____18814 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18814
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
                                            | uu____18839 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___252_18912 = env.effects  in
              { decls = (uu___252_18912.decls); order = order2; joins }  in
            let uu___253_18913 = env  in
            {
              solver = (uu___253_18913.solver);
              range = (uu___253_18913.range);
              curmodule = (uu___253_18913.curmodule);
              gamma = (uu___253_18913.gamma);
              gamma_sig = (uu___253_18913.gamma_sig);
              gamma_cache = (uu___253_18913.gamma_cache);
              modules = (uu___253_18913.modules);
              expected_typ = (uu___253_18913.expected_typ);
              sigtab = (uu___253_18913.sigtab);
              attrtab = (uu___253_18913.attrtab);
              is_pattern = (uu___253_18913.is_pattern);
              instantiate_imp = (uu___253_18913.instantiate_imp);
              effects;
              generalize = (uu___253_18913.generalize);
              letrecs = (uu___253_18913.letrecs);
              top_level = (uu___253_18913.top_level);
              check_uvars = (uu___253_18913.check_uvars);
              use_eq = (uu___253_18913.use_eq);
              is_iface = (uu___253_18913.is_iface);
              admit = (uu___253_18913.admit);
              lax = (uu___253_18913.lax);
              lax_universes = (uu___253_18913.lax_universes);
              phase1 = (uu___253_18913.phase1);
              failhard = (uu___253_18913.failhard);
              nosynth = (uu___253_18913.nosynth);
              uvar_subtyping = (uu___253_18913.uvar_subtyping);
              tc_term = (uu___253_18913.tc_term);
              type_of = (uu___253_18913.type_of);
              universe_of = (uu___253_18913.universe_of);
              check_type_of = (uu___253_18913.check_type_of);
              use_bv_sorts = (uu___253_18913.use_bv_sorts);
              qtbl_name_and_index = (uu___253_18913.qtbl_name_and_index);
              normalized_eff_names = (uu___253_18913.normalized_eff_names);
              proof_ns = (uu___253_18913.proof_ns);
              synth_hook = (uu___253_18913.synth_hook);
              splice = (uu___253_18913.splice);
              is_native_tactic = (uu___253_18913.is_native_tactic);
              identifier_info = (uu___253_18913.identifier_info);
              tc_hooks = (uu___253_18913.tc_hooks);
              dsenv = (uu___253_18913.dsenv);
              nbe = (uu___253_18913.nbe)
            }))
      | uu____18914 -> env
  
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
        | uu____18942 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____18954 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____18954 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____18971 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____18971 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18993 =
                     let uu____18998 =
                       let uu____18999 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____19006 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____19015 =
                         let uu____19016 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____19016  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18999 uu____19006 uu____19015
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18998)
                      in
                   FStar_Errors.raise_error uu____18993
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19021 =
                     let uu____19032 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____19032 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____19069  ->
                        fun uu____19070  ->
                          match (uu____19069, uu____19070) with
                          | ((x,uu____19100),(t,uu____19102)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19021
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19133 =
                     let uu___254_19134 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___254_19134.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___254_19134.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___254_19134.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___254_19134.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19133
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____19145 .
    'Auu____19145 ->
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
          let uu____19175 = effect_decl_opt env effect_name  in
          match uu____19175 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____19214 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19237 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____19274 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____19274
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____19275 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19275
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____19289 =
                     let uu____19292 = get_range env  in
                     let uu____19293 =
                       let uu____19300 =
                         let uu____19301 =
                           let uu____19318 =
                             let uu____19329 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____19329; wp]  in
                           (repr, uu____19318)  in
                         FStar_Syntax_Syntax.Tm_app uu____19301  in
                       FStar_Syntax_Syntax.mk uu____19300  in
                     uu____19293 FStar_Pervasives_Native.None uu____19292  in
                   FStar_Pervasives_Native.Some uu____19289)
  
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
      | uu____19444 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19455 =
        let uu____19456 = FStar_Syntax_Subst.compress t  in
        uu____19456.FStar_Syntax_Syntax.n  in
      match uu____19455 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19459,c) ->
          is_reifiable_comp env c
      | uu____19481 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____19499 =
           let uu____19500 = is_reifiable_effect env l  in
           Prims.op_Negation uu____19500  in
         if uu____19499
         then
           let uu____19501 =
             let uu____19506 =
               let uu____19507 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19507
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19506)  in
           let uu____19508 = get_range env  in
           FStar_Errors.raise_error uu____19501 uu____19508
         else ());
        (let uu____19510 = effect_repr_aux true env c u_c  in
         match uu____19510 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___255_19542 = env  in
        {
          solver = (uu___255_19542.solver);
          range = (uu___255_19542.range);
          curmodule = (uu___255_19542.curmodule);
          gamma = (uu___255_19542.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___255_19542.gamma_cache);
          modules = (uu___255_19542.modules);
          expected_typ = (uu___255_19542.expected_typ);
          sigtab = (uu___255_19542.sigtab);
          attrtab = (uu___255_19542.attrtab);
          is_pattern = (uu___255_19542.is_pattern);
          instantiate_imp = (uu___255_19542.instantiate_imp);
          effects = (uu___255_19542.effects);
          generalize = (uu___255_19542.generalize);
          letrecs = (uu___255_19542.letrecs);
          top_level = (uu___255_19542.top_level);
          check_uvars = (uu___255_19542.check_uvars);
          use_eq = (uu___255_19542.use_eq);
          is_iface = (uu___255_19542.is_iface);
          admit = (uu___255_19542.admit);
          lax = (uu___255_19542.lax);
          lax_universes = (uu___255_19542.lax_universes);
          phase1 = (uu___255_19542.phase1);
          failhard = (uu___255_19542.failhard);
          nosynth = (uu___255_19542.nosynth);
          uvar_subtyping = (uu___255_19542.uvar_subtyping);
          tc_term = (uu___255_19542.tc_term);
          type_of = (uu___255_19542.type_of);
          universe_of = (uu___255_19542.universe_of);
          check_type_of = (uu___255_19542.check_type_of);
          use_bv_sorts = (uu___255_19542.use_bv_sorts);
          qtbl_name_and_index = (uu___255_19542.qtbl_name_and_index);
          normalized_eff_names = (uu___255_19542.normalized_eff_names);
          proof_ns = (uu___255_19542.proof_ns);
          synth_hook = (uu___255_19542.synth_hook);
          splice = (uu___255_19542.splice);
          is_native_tactic = (uu___255_19542.is_native_tactic);
          identifier_info = (uu___255_19542.identifier_info);
          tc_hooks = (uu___255_19542.tc_hooks);
          dsenv = (uu___255_19542.dsenv);
          nbe = (uu___255_19542.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___256_19555 = env  in
      {
        solver = (uu___256_19555.solver);
        range = (uu___256_19555.range);
        curmodule = (uu___256_19555.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___256_19555.gamma_sig);
        gamma_cache = (uu___256_19555.gamma_cache);
        modules = (uu___256_19555.modules);
        expected_typ = (uu___256_19555.expected_typ);
        sigtab = (uu___256_19555.sigtab);
        attrtab = (uu___256_19555.attrtab);
        is_pattern = (uu___256_19555.is_pattern);
        instantiate_imp = (uu___256_19555.instantiate_imp);
        effects = (uu___256_19555.effects);
        generalize = (uu___256_19555.generalize);
        letrecs = (uu___256_19555.letrecs);
        top_level = (uu___256_19555.top_level);
        check_uvars = (uu___256_19555.check_uvars);
        use_eq = (uu___256_19555.use_eq);
        is_iface = (uu___256_19555.is_iface);
        admit = (uu___256_19555.admit);
        lax = (uu___256_19555.lax);
        lax_universes = (uu___256_19555.lax_universes);
        phase1 = (uu___256_19555.phase1);
        failhard = (uu___256_19555.failhard);
        nosynth = (uu___256_19555.nosynth);
        uvar_subtyping = (uu___256_19555.uvar_subtyping);
        tc_term = (uu___256_19555.tc_term);
        type_of = (uu___256_19555.type_of);
        universe_of = (uu___256_19555.universe_of);
        check_type_of = (uu___256_19555.check_type_of);
        use_bv_sorts = (uu___256_19555.use_bv_sorts);
        qtbl_name_and_index = (uu___256_19555.qtbl_name_and_index);
        normalized_eff_names = (uu___256_19555.normalized_eff_names);
        proof_ns = (uu___256_19555.proof_ns);
        synth_hook = (uu___256_19555.synth_hook);
        splice = (uu___256_19555.splice);
        is_native_tactic = (uu___256_19555.is_native_tactic);
        identifier_info = (uu___256_19555.identifier_info);
        tc_hooks = (uu___256_19555.tc_hooks);
        dsenv = (uu___256_19555.dsenv);
        nbe = (uu___256_19555.nbe)
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
            (let uu___257_19610 = env  in
             {
               solver = (uu___257_19610.solver);
               range = (uu___257_19610.range);
               curmodule = (uu___257_19610.curmodule);
               gamma = rest;
               gamma_sig = (uu___257_19610.gamma_sig);
               gamma_cache = (uu___257_19610.gamma_cache);
               modules = (uu___257_19610.modules);
               expected_typ = (uu___257_19610.expected_typ);
               sigtab = (uu___257_19610.sigtab);
               attrtab = (uu___257_19610.attrtab);
               is_pattern = (uu___257_19610.is_pattern);
               instantiate_imp = (uu___257_19610.instantiate_imp);
               effects = (uu___257_19610.effects);
               generalize = (uu___257_19610.generalize);
               letrecs = (uu___257_19610.letrecs);
               top_level = (uu___257_19610.top_level);
               check_uvars = (uu___257_19610.check_uvars);
               use_eq = (uu___257_19610.use_eq);
               is_iface = (uu___257_19610.is_iface);
               admit = (uu___257_19610.admit);
               lax = (uu___257_19610.lax);
               lax_universes = (uu___257_19610.lax_universes);
               phase1 = (uu___257_19610.phase1);
               failhard = (uu___257_19610.failhard);
               nosynth = (uu___257_19610.nosynth);
               uvar_subtyping = (uu___257_19610.uvar_subtyping);
               tc_term = (uu___257_19610.tc_term);
               type_of = (uu___257_19610.type_of);
               universe_of = (uu___257_19610.universe_of);
               check_type_of = (uu___257_19610.check_type_of);
               use_bv_sorts = (uu___257_19610.use_bv_sorts);
               qtbl_name_and_index = (uu___257_19610.qtbl_name_and_index);
               normalized_eff_names = (uu___257_19610.normalized_eff_names);
               proof_ns = (uu___257_19610.proof_ns);
               synth_hook = (uu___257_19610.synth_hook);
               splice = (uu___257_19610.splice);
               is_native_tactic = (uu___257_19610.is_native_tactic);
               identifier_info = (uu___257_19610.identifier_info);
               tc_hooks = (uu___257_19610.tc_hooks);
               dsenv = (uu___257_19610.dsenv);
               nbe = (uu___257_19610.nbe)
             }))
    | uu____19611 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19639  ->
             match uu____19639 with | (x,uu____19647) -> push_bv env1 x) env
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
            let uu___258_19681 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___258_19681.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___258_19681.FStar_Syntax_Syntax.index);
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
      (let uu___259_19721 = env  in
       {
         solver = (uu___259_19721.solver);
         range = (uu___259_19721.range);
         curmodule = (uu___259_19721.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___259_19721.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___259_19721.sigtab);
         attrtab = (uu___259_19721.attrtab);
         is_pattern = (uu___259_19721.is_pattern);
         instantiate_imp = (uu___259_19721.instantiate_imp);
         effects = (uu___259_19721.effects);
         generalize = (uu___259_19721.generalize);
         letrecs = (uu___259_19721.letrecs);
         top_level = (uu___259_19721.top_level);
         check_uvars = (uu___259_19721.check_uvars);
         use_eq = (uu___259_19721.use_eq);
         is_iface = (uu___259_19721.is_iface);
         admit = (uu___259_19721.admit);
         lax = (uu___259_19721.lax);
         lax_universes = (uu___259_19721.lax_universes);
         phase1 = (uu___259_19721.phase1);
         failhard = (uu___259_19721.failhard);
         nosynth = (uu___259_19721.nosynth);
         uvar_subtyping = (uu___259_19721.uvar_subtyping);
         tc_term = (uu___259_19721.tc_term);
         type_of = (uu___259_19721.type_of);
         universe_of = (uu___259_19721.universe_of);
         check_type_of = (uu___259_19721.check_type_of);
         use_bv_sorts = (uu___259_19721.use_bv_sorts);
         qtbl_name_and_index = (uu___259_19721.qtbl_name_and_index);
         normalized_eff_names = (uu___259_19721.normalized_eff_names);
         proof_ns = (uu___259_19721.proof_ns);
         synth_hook = (uu___259_19721.synth_hook);
         splice = (uu___259_19721.splice);
         is_native_tactic = (uu___259_19721.is_native_tactic);
         identifier_info = (uu___259_19721.identifier_info);
         tc_hooks = (uu___259_19721.tc_hooks);
         dsenv = (uu___259_19721.dsenv);
         nbe = (uu___259_19721.nbe)
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
        let uu____19763 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19763 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19791 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19791)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___260_19806 = env  in
      {
        solver = (uu___260_19806.solver);
        range = (uu___260_19806.range);
        curmodule = (uu___260_19806.curmodule);
        gamma = (uu___260_19806.gamma);
        gamma_sig = (uu___260_19806.gamma_sig);
        gamma_cache = (uu___260_19806.gamma_cache);
        modules = (uu___260_19806.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___260_19806.sigtab);
        attrtab = (uu___260_19806.attrtab);
        is_pattern = (uu___260_19806.is_pattern);
        instantiate_imp = (uu___260_19806.instantiate_imp);
        effects = (uu___260_19806.effects);
        generalize = (uu___260_19806.generalize);
        letrecs = (uu___260_19806.letrecs);
        top_level = (uu___260_19806.top_level);
        check_uvars = (uu___260_19806.check_uvars);
        use_eq = false;
        is_iface = (uu___260_19806.is_iface);
        admit = (uu___260_19806.admit);
        lax = (uu___260_19806.lax);
        lax_universes = (uu___260_19806.lax_universes);
        phase1 = (uu___260_19806.phase1);
        failhard = (uu___260_19806.failhard);
        nosynth = (uu___260_19806.nosynth);
        uvar_subtyping = (uu___260_19806.uvar_subtyping);
        tc_term = (uu___260_19806.tc_term);
        type_of = (uu___260_19806.type_of);
        universe_of = (uu___260_19806.universe_of);
        check_type_of = (uu___260_19806.check_type_of);
        use_bv_sorts = (uu___260_19806.use_bv_sorts);
        qtbl_name_and_index = (uu___260_19806.qtbl_name_and_index);
        normalized_eff_names = (uu___260_19806.normalized_eff_names);
        proof_ns = (uu___260_19806.proof_ns);
        synth_hook = (uu___260_19806.synth_hook);
        splice = (uu___260_19806.splice);
        is_native_tactic = (uu___260_19806.is_native_tactic);
        identifier_info = (uu___260_19806.identifier_info);
        tc_hooks = (uu___260_19806.tc_hooks);
        dsenv = (uu___260_19806.dsenv);
        nbe = (uu___260_19806.nbe)
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
    let uu____19834 = expected_typ env_  in
    ((let uu___261_19840 = env_  in
      {
        solver = (uu___261_19840.solver);
        range = (uu___261_19840.range);
        curmodule = (uu___261_19840.curmodule);
        gamma = (uu___261_19840.gamma);
        gamma_sig = (uu___261_19840.gamma_sig);
        gamma_cache = (uu___261_19840.gamma_cache);
        modules = (uu___261_19840.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___261_19840.sigtab);
        attrtab = (uu___261_19840.attrtab);
        is_pattern = (uu___261_19840.is_pattern);
        instantiate_imp = (uu___261_19840.instantiate_imp);
        effects = (uu___261_19840.effects);
        generalize = (uu___261_19840.generalize);
        letrecs = (uu___261_19840.letrecs);
        top_level = (uu___261_19840.top_level);
        check_uvars = (uu___261_19840.check_uvars);
        use_eq = false;
        is_iface = (uu___261_19840.is_iface);
        admit = (uu___261_19840.admit);
        lax = (uu___261_19840.lax);
        lax_universes = (uu___261_19840.lax_universes);
        phase1 = (uu___261_19840.phase1);
        failhard = (uu___261_19840.failhard);
        nosynth = (uu___261_19840.nosynth);
        uvar_subtyping = (uu___261_19840.uvar_subtyping);
        tc_term = (uu___261_19840.tc_term);
        type_of = (uu___261_19840.type_of);
        universe_of = (uu___261_19840.universe_of);
        check_type_of = (uu___261_19840.check_type_of);
        use_bv_sorts = (uu___261_19840.use_bv_sorts);
        qtbl_name_and_index = (uu___261_19840.qtbl_name_and_index);
        normalized_eff_names = (uu___261_19840.normalized_eff_names);
        proof_ns = (uu___261_19840.proof_ns);
        synth_hook = (uu___261_19840.synth_hook);
        splice = (uu___261_19840.splice);
        is_native_tactic = (uu___261_19840.is_native_tactic);
        identifier_info = (uu___261_19840.identifier_info);
        tc_hooks = (uu___261_19840.tc_hooks);
        dsenv = (uu___261_19840.dsenv);
        nbe = (uu___261_19840.nbe)
      }), uu____19834)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19850 =
      let uu____19853 = FStar_Ident.id_of_text ""  in [uu____19853]  in
    FStar_Ident.lid_of_ids uu____19850  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19859 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19859
        then
          let uu____19862 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19862 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___262_19889 = env  in
       {
         solver = (uu___262_19889.solver);
         range = (uu___262_19889.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___262_19889.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___262_19889.expected_typ);
         sigtab = (uu___262_19889.sigtab);
         attrtab = (uu___262_19889.attrtab);
         is_pattern = (uu___262_19889.is_pattern);
         instantiate_imp = (uu___262_19889.instantiate_imp);
         effects = (uu___262_19889.effects);
         generalize = (uu___262_19889.generalize);
         letrecs = (uu___262_19889.letrecs);
         top_level = (uu___262_19889.top_level);
         check_uvars = (uu___262_19889.check_uvars);
         use_eq = (uu___262_19889.use_eq);
         is_iface = (uu___262_19889.is_iface);
         admit = (uu___262_19889.admit);
         lax = (uu___262_19889.lax);
         lax_universes = (uu___262_19889.lax_universes);
         phase1 = (uu___262_19889.phase1);
         failhard = (uu___262_19889.failhard);
         nosynth = (uu___262_19889.nosynth);
         uvar_subtyping = (uu___262_19889.uvar_subtyping);
         tc_term = (uu___262_19889.tc_term);
         type_of = (uu___262_19889.type_of);
         universe_of = (uu___262_19889.universe_of);
         check_type_of = (uu___262_19889.check_type_of);
         use_bv_sorts = (uu___262_19889.use_bv_sorts);
         qtbl_name_and_index = (uu___262_19889.qtbl_name_and_index);
         normalized_eff_names = (uu___262_19889.normalized_eff_names);
         proof_ns = (uu___262_19889.proof_ns);
         synth_hook = (uu___262_19889.synth_hook);
         splice = (uu___262_19889.splice);
         is_native_tactic = (uu___262_19889.is_native_tactic);
         identifier_info = (uu___262_19889.identifier_info);
         tc_hooks = (uu___262_19889.tc_hooks);
         dsenv = (uu___262_19889.dsenv);
         nbe = (uu___262_19889.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19940)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19944,(uu____19945,t)))::tl1
          ->
          let uu____19966 =
            let uu____19969 = FStar_Syntax_Free.uvars t  in
            ext out uu____19969  in
          aux uu____19966 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19972;
            FStar_Syntax_Syntax.index = uu____19973;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19980 =
            let uu____19983 = FStar_Syntax_Free.uvars t  in
            ext out uu____19983  in
          aux uu____19980 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20040)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20044,(uu____20045,t)))::tl1
          ->
          let uu____20066 =
            let uu____20069 = FStar_Syntax_Free.univs t  in
            ext out uu____20069  in
          aux uu____20066 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20072;
            FStar_Syntax_Syntax.index = uu____20073;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20080 =
            let uu____20083 = FStar_Syntax_Free.univs t  in
            ext out uu____20083  in
          aux uu____20080 tl1
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
          let uu____20144 = FStar_Util.set_add uname out  in
          aux uu____20144 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20147,(uu____20148,t)))::tl1
          ->
          let uu____20169 =
            let uu____20172 = FStar_Syntax_Free.univnames t  in
            ext out uu____20172  in
          aux uu____20169 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20175;
            FStar_Syntax_Syntax.index = uu____20176;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20183 =
            let uu____20186 = FStar_Syntax_Free.univnames t  in
            ext out uu____20186  in
          aux uu____20183 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___236_20206  ->
            match uu___236_20206 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20210 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20223 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20233 =
      let uu____20242 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20242
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20233 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20286 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___237_20296  ->
              match uu___237_20296 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20298 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20298
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20301) ->
                  let uu____20318 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20318))
       in
    FStar_All.pipe_right uu____20286 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___238_20325  ->
    match uu___238_20325 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20327 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20327
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20347  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20389) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20408,uu____20409) -> false  in
      let uu____20418 =
        FStar_List.tryFind
          (fun uu____20436  ->
             match uu____20436 with | (p,uu____20444) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20418 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20455,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20477 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20477
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___263_20495 = e  in
        {
          solver = (uu___263_20495.solver);
          range = (uu___263_20495.range);
          curmodule = (uu___263_20495.curmodule);
          gamma = (uu___263_20495.gamma);
          gamma_sig = (uu___263_20495.gamma_sig);
          gamma_cache = (uu___263_20495.gamma_cache);
          modules = (uu___263_20495.modules);
          expected_typ = (uu___263_20495.expected_typ);
          sigtab = (uu___263_20495.sigtab);
          attrtab = (uu___263_20495.attrtab);
          is_pattern = (uu___263_20495.is_pattern);
          instantiate_imp = (uu___263_20495.instantiate_imp);
          effects = (uu___263_20495.effects);
          generalize = (uu___263_20495.generalize);
          letrecs = (uu___263_20495.letrecs);
          top_level = (uu___263_20495.top_level);
          check_uvars = (uu___263_20495.check_uvars);
          use_eq = (uu___263_20495.use_eq);
          is_iface = (uu___263_20495.is_iface);
          admit = (uu___263_20495.admit);
          lax = (uu___263_20495.lax);
          lax_universes = (uu___263_20495.lax_universes);
          phase1 = (uu___263_20495.phase1);
          failhard = (uu___263_20495.failhard);
          nosynth = (uu___263_20495.nosynth);
          uvar_subtyping = (uu___263_20495.uvar_subtyping);
          tc_term = (uu___263_20495.tc_term);
          type_of = (uu___263_20495.type_of);
          universe_of = (uu___263_20495.universe_of);
          check_type_of = (uu___263_20495.check_type_of);
          use_bv_sorts = (uu___263_20495.use_bv_sorts);
          qtbl_name_and_index = (uu___263_20495.qtbl_name_and_index);
          normalized_eff_names = (uu___263_20495.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___263_20495.synth_hook);
          splice = (uu___263_20495.splice);
          is_native_tactic = (uu___263_20495.is_native_tactic);
          identifier_info = (uu___263_20495.identifier_info);
          tc_hooks = (uu___263_20495.tc_hooks);
          dsenv = (uu___263_20495.dsenv);
          nbe = (uu___263_20495.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___264_20535 = e  in
      {
        solver = (uu___264_20535.solver);
        range = (uu___264_20535.range);
        curmodule = (uu___264_20535.curmodule);
        gamma = (uu___264_20535.gamma);
        gamma_sig = (uu___264_20535.gamma_sig);
        gamma_cache = (uu___264_20535.gamma_cache);
        modules = (uu___264_20535.modules);
        expected_typ = (uu___264_20535.expected_typ);
        sigtab = (uu___264_20535.sigtab);
        attrtab = (uu___264_20535.attrtab);
        is_pattern = (uu___264_20535.is_pattern);
        instantiate_imp = (uu___264_20535.instantiate_imp);
        effects = (uu___264_20535.effects);
        generalize = (uu___264_20535.generalize);
        letrecs = (uu___264_20535.letrecs);
        top_level = (uu___264_20535.top_level);
        check_uvars = (uu___264_20535.check_uvars);
        use_eq = (uu___264_20535.use_eq);
        is_iface = (uu___264_20535.is_iface);
        admit = (uu___264_20535.admit);
        lax = (uu___264_20535.lax);
        lax_universes = (uu___264_20535.lax_universes);
        phase1 = (uu___264_20535.phase1);
        failhard = (uu___264_20535.failhard);
        nosynth = (uu___264_20535.nosynth);
        uvar_subtyping = (uu___264_20535.uvar_subtyping);
        tc_term = (uu___264_20535.tc_term);
        type_of = (uu___264_20535.type_of);
        universe_of = (uu___264_20535.universe_of);
        check_type_of = (uu___264_20535.check_type_of);
        use_bv_sorts = (uu___264_20535.use_bv_sorts);
        qtbl_name_and_index = (uu___264_20535.qtbl_name_and_index);
        normalized_eff_names = (uu___264_20535.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___264_20535.synth_hook);
        splice = (uu___264_20535.splice);
        is_native_tactic = (uu___264_20535.is_native_tactic);
        identifier_info = (uu___264_20535.identifier_info);
        tc_hooks = (uu___264_20535.tc_hooks);
        dsenv = (uu___264_20535.dsenv);
        nbe = (uu___264_20535.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20550 = FStar_Syntax_Free.names t  in
      let uu____20553 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20550 uu____20553
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20574 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20574
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20582 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20582
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20599 =
      match uu____20599 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20609 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20609)
       in
    let uu____20611 =
      let uu____20614 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20614 FStar_List.rev  in
    FStar_All.pipe_right uu____20611 (FStar_String.concat " ")
  
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
                  (let uu____20667 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20667 with
                   | FStar_Pervasives_Native.Some uu____20670 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20671 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20677;
        univ_ineqs = uu____20678; implicits = uu____20679;_} -> true
    | uu____20690 -> false
  
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
          let uu___265_20717 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___265_20717.deferred);
            univ_ineqs = (uu___265_20717.univ_ineqs);
            implicits = (uu___265_20717.implicits)
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
          let uu____20752 = FStar_Options.defensive ()  in
          if uu____20752
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20756 =
              let uu____20757 =
                let uu____20758 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20758  in
              Prims.op_Negation uu____20757  in
            (if uu____20756
             then
               let uu____20763 =
                 let uu____20768 =
                   let uu____20769 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20770 =
                     let uu____20771 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20771
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20769 uu____20770
                    in
                 (FStar_Errors.Warning_Defensive, uu____20768)  in
               FStar_Errors.log_issue rng uu____20763
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
          let uu____20802 =
            let uu____20803 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20803  in
          if uu____20802
          then ()
          else
            (let uu____20805 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20805 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20828 =
            let uu____20829 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20829  in
          if uu____20828
          then ()
          else
            (let uu____20831 = bound_vars e  in
             def_check_closed_in rng msg uu____20831 t)
  
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
          let uu___266_20866 = g  in
          let uu____20867 =
            let uu____20868 =
              let uu____20869 =
                let uu____20876 =
                  let uu____20877 =
                    let uu____20894 =
                      let uu____20905 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20905]  in
                    (f, uu____20894)  in
                  FStar_Syntax_Syntax.Tm_app uu____20877  in
                FStar_Syntax_Syntax.mk uu____20876  in
              uu____20869 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20868
             in
          {
            guard_f = uu____20867;
            deferred = (uu___266_20866.deferred);
            univ_ineqs = (uu___266_20866.univ_ineqs);
            implicits = (uu___266_20866.implicits)
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
          let uu___267_20961 = g  in
          let uu____20962 =
            let uu____20963 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20963  in
          {
            guard_f = uu____20962;
            deferred = (uu___267_20961.deferred);
            univ_ineqs = (uu___267_20961.univ_ineqs);
            implicits = (uu___267_20961.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___268_20979 = g  in
          let uu____20980 =
            let uu____20981 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____20981  in
          {
            guard_f = uu____20980;
            deferred = (uu___268_20979.deferred);
            univ_ineqs = (uu___268_20979.univ_ineqs);
            implicits = (uu___268_20979.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___269_20983 = g  in
          let uu____20984 =
            let uu____20985 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20985  in
          {
            guard_f = uu____20984;
            deferred = (uu___269_20983.deferred);
            univ_ineqs = (uu___269_20983.univ_ineqs);
            implicits = (uu___269_20983.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20991 ->
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
          let uu____21006 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____21006
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____21012 =
      let uu____21013 = FStar_Syntax_Util.unmeta t  in
      uu____21013.FStar_Syntax_Syntax.n  in
    match uu____21012 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21017 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____21058 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____21058;
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
                       let uu____21148 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21148
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___270_21152 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___270_21152.deferred);
              univ_ineqs = (uu___270_21152.univ_ineqs);
              implicits = (uu___270_21152.implicits)
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
               let uu____21185 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21185
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
            let uu___271_21208 = g  in
            let uu____21209 =
              let uu____21210 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21210  in
            {
              guard_f = uu____21209;
              deferred = (uu___271_21208.deferred);
              univ_ineqs = (uu___271_21208.univ_ineqs);
              implicits = (uu___271_21208.implicits)
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
            let uu____21248 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21248 with
            | FStar_Pervasives_Native.Some
                (uu____21273::(tm,uu____21275)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21339 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21357 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21357;
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
                    let uu___272_21392 = trivial_guard  in
                    {
                      guard_f = (uu___272_21392.guard_f);
                      deferred = (uu___272_21392.deferred);
                      univ_ineqs = (uu___272_21392.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21409  -> ());
    push = (fun uu____21411  -> ());
    pop = (fun uu____21413  -> ());
    snapshot =
      (fun uu____21415  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21424  -> fun uu____21425  -> ());
    encode_modul = (fun uu____21436  -> fun uu____21437  -> ());
    encode_sig = (fun uu____21440  -> fun uu____21441  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21447 =
             let uu____21454 = FStar_Options.peek ()  in (e, g, uu____21454)
              in
           [uu____21447]);
    solve = (fun uu____21470  -> fun uu____21471  -> fun uu____21472  -> ());
    finish = (fun uu____21478  -> ());
    refresh = (fun uu____21480  -> ())
  } 