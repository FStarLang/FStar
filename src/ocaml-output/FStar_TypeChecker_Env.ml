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
           (fun uu___225_9662  ->
              match uu___225_9662 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9665 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____9665  in
                  let uu____9666 =
                    let uu____9667 = FStar_Syntax_Subst.compress y  in
                    uu____9667.FStar_Syntax_Syntax.n  in
                  (match uu____9666 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9671 =
                         let uu___239_9672 = y1  in
                         let uu____9673 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___239_9672.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___239_9672.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9673
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____9671
                   | uu____9676 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___240_9688 = env  in
      let uu____9689 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___240_9688.solver);
        range = (uu___240_9688.range);
        curmodule = (uu___240_9688.curmodule);
        gamma = uu____9689;
        gamma_sig = (uu___240_9688.gamma_sig);
        gamma_cache = (uu___240_9688.gamma_cache);
        modules = (uu___240_9688.modules);
        expected_typ = (uu___240_9688.expected_typ);
        sigtab = (uu___240_9688.sigtab);
        attrtab = (uu___240_9688.attrtab);
        is_pattern = (uu___240_9688.is_pattern);
        instantiate_imp = (uu___240_9688.instantiate_imp);
        effects = (uu___240_9688.effects);
        generalize = (uu___240_9688.generalize);
        letrecs = (uu___240_9688.letrecs);
        top_level = (uu___240_9688.top_level);
        check_uvars = (uu___240_9688.check_uvars);
        use_eq = (uu___240_9688.use_eq);
        is_iface = (uu___240_9688.is_iface);
        admit = (uu___240_9688.admit);
        lax = (uu___240_9688.lax);
        lax_universes = (uu___240_9688.lax_universes);
        phase1 = (uu___240_9688.phase1);
        failhard = (uu___240_9688.failhard);
        nosynth = (uu___240_9688.nosynth);
        uvar_subtyping = (uu___240_9688.uvar_subtyping);
        tc_term = (uu___240_9688.tc_term);
        type_of = (uu___240_9688.type_of);
        universe_of = (uu___240_9688.universe_of);
        check_type_of = (uu___240_9688.check_type_of);
        use_bv_sorts = (uu___240_9688.use_bv_sorts);
        qtbl_name_and_index = (uu___240_9688.qtbl_name_and_index);
        normalized_eff_names = (uu___240_9688.normalized_eff_names);
        proof_ns = (uu___240_9688.proof_ns);
        synth_hook = (uu___240_9688.synth_hook);
        splice = (uu___240_9688.splice);
        is_native_tactic = (uu___240_9688.is_native_tactic);
        identifier_info = (uu___240_9688.identifier_info);
        tc_hooks = (uu___240_9688.tc_hooks);
        dsenv = (uu___240_9688.dsenv);
        nbe = (uu___240_9688.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9696  -> fun uu____9697  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___241_9717 = env  in
      {
        solver = (uu___241_9717.solver);
        range = (uu___241_9717.range);
        curmodule = (uu___241_9717.curmodule);
        gamma = (uu___241_9717.gamma);
        gamma_sig = (uu___241_9717.gamma_sig);
        gamma_cache = (uu___241_9717.gamma_cache);
        modules = (uu___241_9717.modules);
        expected_typ = (uu___241_9717.expected_typ);
        sigtab = (uu___241_9717.sigtab);
        attrtab = (uu___241_9717.attrtab);
        is_pattern = (uu___241_9717.is_pattern);
        instantiate_imp = (uu___241_9717.instantiate_imp);
        effects = (uu___241_9717.effects);
        generalize = (uu___241_9717.generalize);
        letrecs = (uu___241_9717.letrecs);
        top_level = (uu___241_9717.top_level);
        check_uvars = (uu___241_9717.check_uvars);
        use_eq = (uu___241_9717.use_eq);
        is_iface = (uu___241_9717.is_iface);
        admit = (uu___241_9717.admit);
        lax = (uu___241_9717.lax);
        lax_universes = (uu___241_9717.lax_universes);
        phase1 = (uu___241_9717.phase1);
        failhard = (uu___241_9717.failhard);
        nosynth = (uu___241_9717.nosynth);
        uvar_subtyping = (uu___241_9717.uvar_subtyping);
        tc_term = (uu___241_9717.tc_term);
        type_of = (uu___241_9717.type_of);
        universe_of = (uu___241_9717.universe_of);
        check_type_of = (uu___241_9717.check_type_of);
        use_bv_sorts = (uu___241_9717.use_bv_sorts);
        qtbl_name_and_index = (uu___241_9717.qtbl_name_and_index);
        normalized_eff_names = (uu___241_9717.normalized_eff_names);
        proof_ns = (uu___241_9717.proof_ns);
        synth_hook = (uu___241_9717.synth_hook);
        splice = (uu___241_9717.splice);
        is_native_tactic = (uu___241_9717.is_native_tactic);
        identifier_info = (uu___241_9717.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___241_9717.dsenv);
        nbe = (uu___241_9717.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___242_9728 = e  in
      let uu____9729 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___242_9728.solver);
        range = (uu___242_9728.range);
        curmodule = (uu___242_9728.curmodule);
        gamma = (uu___242_9728.gamma);
        gamma_sig = (uu___242_9728.gamma_sig);
        gamma_cache = (uu___242_9728.gamma_cache);
        modules = (uu___242_9728.modules);
        expected_typ = (uu___242_9728.expected_typ);
        sigtab = (uu___242_9728.sigtab);
        attrtab = (uu___242_9728.attrtab);
        is_pattern = (uu___242_9728.is_pattern);
        instantiate_imp = (uu___242_9728.instantiate_imp);
        effects = (uu___242_9728.effects);
        generalize = (uu___242_9728.generalize);
        letrecs = (uu___242_9728.letrecs);
        top_level = (uu___242_9728.top_level);
        check_uvars = (uu___242_9728.check_uvars);
        use_eq = (uu___242_9728.use_eq);
        is_iface = (uu___242_9728.is_iface);
        admit = (uu___242_9728.admit);
        lax = (uu___242_9728.lax);
        lax_universes = (uu___242_9728.lax_universes);
        phase1 = (uu___242_9728.phase1);
        failhard = (uu___242_9728.failhard);
        nosynth = (uu___242_9728.nosynth);
        uvar_subtyping = (uu___242_9728.uvar_subtyping);
        tc_term = (uu___242_9728.tc_term);
        type_of = (uu___242_9728.type_of);
        universe_of = (uu___242_9728.universe_of);
        check_type_of = (uu___242_9728.check_type_of);
        use_bv_sorts = (uu___242_9728.use_bv_sorts);
        qtbl_name_and_index = (uu___242_9728.qtbl_name_and_index);
        normalized_eff_names = (uu___242_9728.normalized_eff_names);
        proof_ns = (uu___242_9728.proof_ns);
        synth_hook = (uu___242_9728.synth_hook);
        splice = (uu___242_9728.splice);
        is_native_tactic = (uu___242_9728.is_native_tactic);
        identifier_info = (uu___242_9728.identifier_info);
        tc_hooks = (uu___242_9728.tc_hooks);
        dsenv = uu____9729;
        nbe = (uu___242_9728.nbe)
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
      | (NoDelta ,uu____9752) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____9753,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____9754,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____9755 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____9764 . unit -> 'Auu____9764 FStar_Util.smap =
  fun uu____9771  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____9776 . unit -> 'Auu____9776 FStar_Util.smap =
  fun uu____9783  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____9917 = new_gamma_cache ()  in
                  let uu____9920 = new_sigtab ()  in
                  let uu____9923 = new_sigtab ()  in
                  let uu____9930 =
                    let uu____9943 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____9943, FStar_Pervasives_Native.None)  in
                  let uu____9958 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____9961 = FStar_Options.using_facts_from ()  in
                  let uu____9962 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____9965 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____9917;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____9920;
                    attrtab = uu____9923;
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
                    qtbl_name_and_index = uu____9930;
                    normalized_eff_names = uu____9958;
                    proof_ns = uu____9961;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10001  -> false);
                    identifier_info = uu____9962;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____9965;
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
  fun uu____10101  ->
    let uu____10102 = FStar_ST.op_Bang query_indices  in
    match uu____10102 with
    | [] -> failwith "Empty query indices!"
    | uu____10152 ->
        let uu____10161 =
          let uu____10170 =
            let uu____10177 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10177  in
          let uu____10227 = FStar_ST.op_Bang query_indices  in uu____10170 ::
            uu____10227
           in
        FStar_ST.op_Colon_Equals query_indices uu____10161
  
let (pop_query_indices : unit -> unit) =
  fun uu____10316  ->
    let uu____10317 = FStar_ST.op_Bang query_indices  in
    match uu____10317 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10432  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10462  ->
    match uu____10462 with
    | (l,n1) ->
        let uu____10469 = FStar_ST.op_Bang query_indices  in
        (match uu____10469 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10580 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10599  ->
    let uu____10600 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10600
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____10673 =
       let uu____10676 = FStar_ST.op_Bang stack  in env :: uu____10676  in
     FStar_ST.op_Colon_Equals stack uu____10673);
    (let uu___243_10725 = env  in
     let uu____10726 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____10729 = FStar_Util.smap_copy (sigtab env)  in
     let uu____10732 = FStar_Util.smap_copy (attrtab env)  in
     let uu____10739 =
       let uu____10752 =
         let uu____10755 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____10755  in
       let uu____10780 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____10752, uu____10780)  in
     let uu____10821 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____10824 =
       let uu____10827 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____10827  in
     {
       solver = (uu___243_10725.solver);
       range = (uu___243_10725.range);
       curmodule = (uu___243_10725.curmodule);
       gamma = (uu___243_10725.gamma);
       gamma_sig = (uu___243_10725.gamma_sig);
       gamma_cache = uu____10726;
       modules = (uu___243_10725.modules);
       expected_typ = (uu___243_10725.expected_typ);
       sigtab = uu____10729;
       attrtab = uu____10732;
       is_pattern = (uu___243_10725.is_pattern);
       instantiate_imp = (uu___243_10725.instantiate_imp);
       effects = (uu___243_10725.effects);
       generalize = (uu___243_10725.generalize);
       letrecs = (uu___243_10725.letrecs);
       top_level = (uu___243_10725.top_level);
       check_uvars = (uu___243_10725.check_uvars);
       use_eq = (uu___243_10725.use_eq);
       is_iface = (uu___243_10725.is_iface);
       admit = (uu___243_10725.admit);
       lax = (uu___243_10725.lax);
       lax_universes = (uu___243_10725.lax_universes);
       phase1 = (uu___243_10725.phase1);
       failhard = (uu___243_10725.failhard);
       nosynth = (uu___243_10725.nosynth);
       uvar_subtyping = (uu___243_10725.uvar_subtyping);
       tc_term = (uu___243_10725.tc_term);
       type_of = (uu___243_10725.type_of);
       universe_of = (uu___243_10725.universe_of);
       check_type_of = (uu___243_10725.check_type_of);
       use_bv_sorts = (uu___243_10725.use_bv_sorts);
       qtbl_name_and_index = uu____10739;
       normalized_eff_names = uu____10821;
       proof_ns = (uu___243_10725.proof_ns);
       synth_hook = (uu___243_10725.synth_hook);
       splice = (uu___243_10725.splice);
       is_native_tactic = (uu___243_10725.is_native_tactic);
       identifier_info = uu____10824;
       tc_hooks = (uu___243_10725.tc_hooks);
       dsenv = (uu___243_10725.dsenv);
       nbe = (uu___243_10725.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____10873  ->
    let uu____10874 = FStar_ST.op_Bang stack  in
    match uu____10874 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10928 -> failwith "Impossible: Too many pops"
  
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
        (fun uu____11000  ->
           let uu____11001 = snapshot_stack env  in
           match uu____11001 with
           | (stack_depth,env1) ->
               let uu____11026 = snapshot_query_indices ()  in
               (match uu____11026 with
                | (query_indices_depth,()) ->
                    let uu____11050 = (env1.solver).snapshot msg  in
                    (match uu____11050 with
                     | (solver_depth,()) ->
                         let uu____11092 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11092 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___244_11138 = env1  in
                                 {
                                   solver = (uu___244_11138.solver);
                                   range = (uu___244_11138.range);
                                   curmodule = (uu___244_11138.curmodule);
                                   gamma = (uu___244_11138.gamma);
                                   gamma_sig = (uu___244_11138.gamma_sig);
                                   gamma_cache = (uu___244_11138.gamma_cache);
                                   modules = (uu___244_11138.modules);
                                   expected_typ =
                                     (uu___244_11138.expected_typ);
                                   sigtab = (uu___244_11138.sigtab);
                                   attrtab = (uu___244_11138.attrtab);
                                   is_pattern = (uu___244_11138.is_pattern);
                                   instantiate_imp =
                                     (uu___244_11138.instantiate_imp);
                                   effects = (uu___244_11138.effects);
                                   generalize = (uu___244_11138.generalize);
                                   letrecs = (uu___244_11138.letrecs);
                                   top_level = (uu___244_11138.top_level);
                                   check_uvars = (uu___244_11138.check_uvars);
                                   use_eq = (uu___244_11138.use_eq);
                                   is_iface = (uu___244_11138.is_iface);
                                   admit = (uu___244_11138.admit);
                                   lax = (uu___244_11138.lax);
                                   lax_universes =
                                     (uu___244_11138.lax_universes);
                                   phase1 = (uu___244_11138.phase1);
                                   failhard = (uu___244_11138.failhard);
                                   nosynth = (uu___244_11138.nosynth);
                                   uvar_subtyping =
                                     (uu___244_11138.uvar_subtyping);
                                   tc_term = (uu___244_11138.tc_term);
                                   type_of = (uu___244_11138.type_of);
                                   universe_of = (uu___244_11138.universe_of);
                                   check_type_of =
                                     (uu___244_11138.check_type_of);
                                   use_bv_sorts =
                                     (uu___244_11138.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___244_11138.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___244_11138.normalized_eff_names);
                                   proof_ns = (uu___244_11138.proof_ns);
                                   synth_hook = (uu___244_11138.synth_hook);
                                   splice = (uu___244_11138.splice);
                                   is_native_tactic =
                                     (uu___244_11138.is_native_tactic);
                                   identifier_info =
                                     (uu___244_11138.identifier_info);
                                   tc_hooks = (uu___244_11138.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___244_11138.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11169  ->
             let uu____11170 =
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
             match uu____11170 with
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
                             ((let uu____11296 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11296
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11307 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11307
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11334,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11366 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11392  ->
                  match uu____11392 with
                  | (m,uu____11398) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11366 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___245_11406 = env  in
               {
                 solver = (uu___245_11406.solver);
                 range = (uu___245_11406.range);
                 curmodule = (uu___245_11406.curmodule);
                 gamma = (uu___245_11406.gamma);
                 gamma_sig = (uu___245_11406.gamma_sig);
                 gamma_cache = (uu___245_11406.gamma_cache);
                 modules = (uu___245_11406.modules);
                 expected_typ = (uu___245_11406.expected_typ);
                 sigtab = (uu___245_11406.sigtab);
                 attrtab = (uu___245_11406.attrtab);
                 is_pattern = (uu___245_11406.is_pattern);
                 instantiate_imp = (uu___245_11406.instantiate_imp);
                 effects = (uu___245_11406.effects);
                 generalize = (uu___245_11406.generalize);
                 letrecs = (uu___245_11406.letrecs);
                 top_level = (uu___245_11406.top_level);
                 check_uvars = (uu___245_11406.check_uvars);
                 use_eq = (uu___245_11406.use_eq);
                 is_iface = (uu___245_11406.is_iface);
                 admit = (uu___245_11406.admit);
                 lax = (uu___245_11406.lax);
                 lax_universes = (uu___245_11406.lax_universes);
                 phase1 = (uu___245_11406.phase1);
                 failhard = (uu___245_11406.failhard);
                 nosynth = (uu___245_11406.nosynth);
                 uvar_subtyping = (uu___245_11406.uvar_subtyping);
                 tc_term = (uu___245_11406.tc_term);
                 type_of = (uu___245_11406.type_of);
                 universe_of = (uu___245_11406.universe_of);
                 check_type_of = (uu___245_11406.check_type_of);
                 use_bv_sorts = (uu___245_11406.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___245_11406.normalized_eff_names);
                 proof_ns = (uu___245_11406.proof_ns);
                 synth_hook = (uu___245_11406.synth_hook);
                 splice = (uu___245_11406.splice);
                 is_native_tactic = (uu___245_11406.is_native_tactic);
                 identifier_info = (uu___245_11406.identifier_info);
                 tc_hooks = (uu___245_11406.tc_hooks);
                 dsenv = (uu___245_11406.dsenv);
                 nbe = (uu___245_11406.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11419,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___246_11428 = env  in
               {
                 solver = (uu___246_11428.solver);
                 range = (uu___246_11428.range);
                 curmodule = (uu___246_11428.curmodule);
                 gamma = (uu___246_11428.gamma);
                 gamma_sig = (uu___246_11428.gamma_sig);
                 gamma_cache = (uu___246_11428.gamma_cache);
                 modules = (uu___246_11428.modules);
                 expected_typ = (uu___246_11428.expected_typ);
                 sigtab = (uu___246_11428.sigtab);
                 attrtab = (uu___246_11428.attrtab);
                 is_pattern = (uu___246_11428.is_pattern);
                 instantiate_imp = (uu___246_11428.instantiate_imp);
                 effects = (uu___246_11428.effects);
                 generalize = (uu___246_11428.generalize);
                 letrecs = (uu___246_11428.letrecs);
                 top_level = (uu___246_11428.top_level);
                 check_uvars = (uu___246_11428.check_uvars);
                 use_eq = (uu___246_11428.use_eq);
                 is_iface = (uu___246_11428.is_iface);
                 admit = (uu___246_11428.admit);
                 lax = (uu___246_11428.lax);
                 lax_universes = (uu___246_11428.lax_universes);
                 phase1 = (uu___246_11428.phase1);
                 failhard = (uu___246_11428.failhard);
                 nosynth = (uu___246_11428.nosynth);
                 uvar_subtyping = (uu___246_11428.uvar_subtyping);
                 tc_term = (uu___246_11428.tc_term);
                 type_of = (uu___246_11428.type_of);
                 universe_of = (uu___246_11428.universe_of);
                 check_type_of = (uu___246_11428.check_type_of);
                 use_bv_sorts = (uu___246_11428.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___246_11428.normalized_eff_names);
                 proof_ns = (uu___246_11428.proof_ns);
                 synth_hook = (uu___246_11428.synth_hook);
                 splice = (uu___246_11428.splice);
                 is_native_tactic = (uu___246_11428.is_native_tactic);
                 identifier_info = (uu___246_11428.identifier_info);
                 tc_hooks = (uu___246_11428.tc_hooks);
                 dsenv = (uu___246_11428.dsenv);
                 nbe = (uu___246_11428.nbe)
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
        (let uu___247_11462 = e  in
         {
           solver = (uu___247_11462.solver);
           range = r;
           curmodule = (uu___247_11462.curmodule);
           gamma = (uu___247_11462.gamma);
           gamma_sig = (uu___247_11462.gamma_sig);
           gamma_cache = (uu___247_11462.gamma_cache);
           modules = (uu___247_11462.modules);
           expected_typ = (uu___247_11462.expected_typ);
           sigtab = (uu___247_11462.sigtab);
           attrtab = (uu___247_11462.attrtab);
           is_pattern = (uu___247_11462.is_pattern);
           instantiate_imp = (uu___247_11462.instantiate_imp);
           effects = (uu___247_11462.effects);
           generalize = (uu___247_11462.generalize);
           letrecs = (uu___247_11462.letrecs);
           top_level = (uu___247_11462.top_level);
           check_uvars = (uu___247_11462.check_uvars);
           use_eq = (uu___247_11462.use_eq);
           is_iface = (uu___247_11462.is_iface);
           admit = (uu___247_11462.admit);
           lax = (uu___247_11462.lax);
           lax_universes = (uu___247_11462.lax_universes);
           phase1 = (uu___247_11462.phase1);
           failhard = (uu___247_11462.failhard);
           nosynth = (uu___247_11462.nosynth);
           uvar_subtyping = (uu___247_11462.uvar_subtyping);
           tc_term = (uu___247_11462.tc_term);
           type_of = (uu___247_11462.type_of);
           universe_of = (uu___247_11462.universe_of);
           check_type_of = (uu___247_11462.check_type_of);
           use_bv_sorts = (uu___247_11462.use_bv_sorts);
           qtbl_name_and_index = (uu___247_11462.qtbl_name_and_index);
           normalized_eff_names = (uu___247_11462.normalized_eff_names);
           proof_ns = (uu___247_11462.proof_ns);
           synth_hook = (uu___247_11462.synth_hook);
           splice = (uu___247_11462.splice);
           is_native_tactic = (uu___247_11462.is_native_tactic);
           identifier_info = (uu___247_11462.identifier_info);
           tc_hooks = (uu___247_11462.tc_hooks);
           dsenv = (uu___247_11462.dsenv);
           nbe = (uu___247_11462.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11478 =
        let uu____11479 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11479 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11478
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11533 =
          let uu____11534 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11534 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11533
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11588 =
          let uu____11589 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11589 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11588
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____11643 =
        let uu____11644 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____11644 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11643
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___248_11705 = env  in
      {
        solver = (uu___248_11705.solver);
        range = (uu___248_11705.range);
        curmodule = lid;
        gamma = (uu___248_11705.gamma);
        gamma_sig = (uu___248_11705.gamma_sig);
        gamma_cache = (uu___248_11705.gamma_cache);
        modules = (uu___248_11705.modules);
        expected_typ = (uu___248_11705.expected_typ);
        sigtab = (uu___248_11705.sigtab);
        attrtab = (uu___248_11705.attrtab);
        is_pattern = (uu___248_11705.is_pattern);
        instantiate_imp = (uu___248_11705.instantiate_imp);
        effects = (uu___248_11705.effects);
        generalize = (uu___248_11705.generalize);
        letrecs = (uu___248_11705.letrecs);
        top_level = (uu___248_11705.top_level);
        check_uvars = (uu___248_11705.check_uvars);
        use_eq = (uu___248_11705.use_eq);
        is_iface = (uu___248_11705.is_iface);
        admit = (uu___248_11705.admit);
        lax = (uu___248_11705.lax);
        lax_universes = (uu___248_11705.lax_universes);
        phase1 = (uu___248_11705.phase1);
        failhard = (uu___248_11705.failhard);
        nosynth = (uu___248_11705.nosynth);
        uvar_subtyping = (uu___248_11705.uvar_subtyping);
        tc_term = (uu___248_11705.tc_term);
        type_of = (uu___248_11705.type_of);
        universe_of = (uu___248_11705.universe_of);
        check_type_of = (uu___248_11705.check_type_of);
        use_bv_sorts = (uu___248_11705.use_bv_sorts);
        qtbl_name_and_index = (uu___248_11705.qtbl_name_and_index);
        normalized_eff_names = (uu___248_11705.normalized_eff_names);
        proof_ns = (uu___248_11705.proof_ns);
        synth_hook = (uu___248_11705.synth_hook);
        splice = (uu___248_11705.splice);
        is_native_tactic = (uu___248_11705.is_native_tactic);
        identifier_info = (uu___248_11705.identifier_info);
        tc_hooks = (uu___248_11705.tc_hooks);
        dsenv = (uu___248_11705.dsenv);
        nbe = (uu___248_11705.nbe)
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
      let uu____11732 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____11732
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____11742 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____11742)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____11752 =
      let uu____11753 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11753  in
    (FStar_Errors.Fatal_VariableNotFound, uu____11752)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11758  ->
    let uu____11759 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____11759
  
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
      | ((formals,t),uu____11853) ->
          let vs = mk_univ_subst formals us  in
          let uu____11877 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____11877)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___226_11893  ->
    match uu___226_11893 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11919  -> new_u_univ ()))
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
      let uu____11938 = inst_tscheme t  in
      match uu____11938 with
      | (us,t1) ->
          let uu____11949 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____11949)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____11969  ->
          match uu____11969 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11990 =
                         let uu____11991 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____11992 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____11993 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____11994 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11991 uu____11992 uu____11993 uu____11994
                          in
                       failwith uu____11990)
                    else ();
                    (let uu____11996 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____11996))
               | uu____12005 ->
                   let uu____12006 =
                     let uu____12007 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12007
                      in
                   failwith uu____12006)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12013 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12019 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12025 -> false
  
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
             | ([],uu____12067) -> Maybe
             | (uu____12074,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12093 -> No  in
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
          let uu____12184 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12184 with
          | FStar_Pervasives_Native.None  ->
              let uu____12207 =
                FStar_Util.find_map env.gamma
                  (fun uu___227_12251  ->
                     match uu___227_12251 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12290 = FStar_Ident.lid_equals lid l  in
                         if uu____12290
                         then
                           let uu____12311 =
                             let uu____12330 =
                               let uu____12345 = inst_tscheme t  in
                               FStar_Util.Inl uu____12345  in
                             let uu____12360 = FStar_Ident.range_of_lid l  in
                             (uu____12330, uu____12360)  in
                           FStar_Pervasives_Native.Some uu____12311
                         else FStar_Pervasives_Native.None
                     | uu____12412 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12207
                (fun uu____12450  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___228_12459  ->
                        match uu___228_12459 with
                        | (uu____12462,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12464);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12465;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12466;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12467;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12468;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12488 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12488
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
                                  uu____12536 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12543 -> cache t  in
                            let uu____12544 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12544 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12550 =
                                   let uu____12551 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12551)
                                    in
                                 maybe_cache uu____12550)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12619 = find_in_sigtab env lid  in
         match uu____12619 with
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
      let uu____12699 = lookup_qname env lid  in
      match uu____12699 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12720,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____12831 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____12831 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____12873 =
          let uu____12876 = lookup_attr env1 attr  in se1 :: uu____12876  in
        FStar_Util.smap_add (attrtab env1) attr uu____12873  in
      FStar_List.iter
        (fun attr  ->
           let uu____12886 =
             let uu____12887 = FStar_Syntax_Subst.compress attr  in
             uu____12887.FStar_Syntax_Syntax.n  in
           match uu____12886 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____12891 =
                 let uu____12892 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____12892.FStar_Ident.str  in
               add_one1 env se uu____12891
           | uu____12893 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12915) ->
          add_sigelts env ses
      | uu____12924 ->
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
            | uu____12939 -> ()))

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
        (fun uu___229_12970  ->
           match uu___229_12970 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12988 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13049,lb::[]),uu____13051) ->
            let uu____13058 =
              let uu____13067 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13076 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13067, uu____13076)  in
            FStar_Pervasives_Native.Some uu____13058
        | FStar_Syntax_Syntax.Sig_let ((uu____13089,lbs),uu____13091) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13121 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13133 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13133
                     then
                       let uu____13144 =
                         let uu____13153 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13162 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13153, uu____13162)  in
                       FStar_Pervasives_Native.Some uu____13144
                     else FStar_Pervasives_Native.None)
        | uu____13184 -> FStar_Pervasives_Native.None
  
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
          let uu____13243 =
            let uu____13252 =
              let uu____13257 =
                let uu____13258 =
                  let uu____13261 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13261
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13258)  in
              inst_tscheme1 uu____13257  in
            (uu____13252, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13243
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13283,uu____13284) ->
          let uu____13289 =
            let uu____13298 =
              let uu____13303 =
                let uu____13304 =
                  let uu____13307 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13307  in
                (us, uu____13304)  in
              inst_tscheme1 uu____13303  in
            (uu____13298, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13289
      | uu____13326 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____13414 =
          match uu____13414 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13510,uvs,t,uu____13513,uu____13514,uu____13515);
                      FStar_Syntax_Syntax.sigrng = uu____13516;
                      FStar_Syntax_Syntax.sigquals = uu____13517;
                      FStar_Syntax_Syntax.sigmeta = uu____13518;
                      FStar_Syntax_Syntax.sigattrs = uu____13519;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13540 =
                     let uu____13549 = inst_tscheme1 (uvs, t)  in
                     (uu____13549, rng)  in
                   FStar_Pervasives_Native.Some uu____13540
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13573;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13575;
                      FStar_Syntax_Syntax.sigattrs = uu____13576;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13593 =
                     let uu____13594 = in_cur_mod env l  in uu____13594 = Yes
                      in
                   if uu____13593
                   then
                     let uu____13605 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13605
                      then
                        let uu____13618 =
                          let uu____13627 = inst_tscheme1 (uvs, t)  in
                          (uu____13627, rng)  in
                        FStar_Pervasives_Native.Some uu____13618
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13658 =
                        let uu____13667 = inst_tscheme1 (uvs, t)  in
                        (uu____13667, rng)  in
                      FStar_Pervasives_Native.Some uu____13658)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13692,uu____13693);
                      FStar_Syntax_Syntax.sigrng = uu____13694;
                      FStar_Syntax_Syntax.sigquals = uu____13695;
                      FStar_Syntax_Syntax.sigmeta = uu____13696;
                      FStar_Syntax_Syntax.sigattrs = uu____13697;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____13738 =
                          let uu____13747 = inst_tscheme1 (uvs, k)  in
                          (uu____13747, rng)  in
                        FStar_Pervasives_Native.Some uu____13738
                    | uu____13768 ->
                        let uu____13769 =
                          let uu____13778 =
                            let uu____13783 =
                              let uu____13784 =
                                let uu____13787 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13787
                                 in
                              (uvs, uu____13784)  in
                            inst_tscheme1 uu____13783  in
                          (uu____13778, rng)  in
                        FStar_Pervasives_Native.Some uu____13769)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____13810,uu____13811);
                      FStar_Syntax_Syntax.sigrng = uu____13812;
                      FStar_Syntax_Syntax.sigquals = uu____13813;
                      FStar_Syntax_Syntax.sigmeta = uu____13814;
                      FStar_Syntax_Syntax.sigattrs = uu____13815;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13857 =
                          let uu____13866 = inst_tscheme_with (uvs, k) us  in
                          (uu____13866, rng)  in
                        FStar_Pervasives_Native.Some uu____13857
                    | uu____13887 ->
                        let uu____13888 =
                          let uu____13897 =
                            let uu____13902 =
                              let uu____13903 =
                                let uu____13906 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____13906
                                 in
                              (uvs, uu____13903)  in
                            inst_tscheme_with uu____13902 us  in
                          (uu____13897, rng)  in
                        FStar_Pervasives_Native.Some uu____13888)
               | FStar_Util.Inr se ->
                   let uu____13942 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13963;
                          FStar_Syntax_Syntax.sigrng = uu____13964;
                          FStar_Syntax_Syntax.sigquals = uu____13965;
                          FStar_Syntax_Syntax.sigmeta = uu____13966;
                          FStar_Syntax_Syntax.sigattrs = uu____13967;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13982 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____13942
                     (FStar_Util.map_option
                        (fun uu____14030  ->
                           match uu____14030 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14061 =
          let uu____14072 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14072 mapper  in
        match uu____14061 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14146 =
              let uu____14157 =
                let uu____14164 =
                  let uu___249_14167 = t  in
                  let uu____14168 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___249_14167.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14168;
                    FStar_Syntax_Syntax.vars =
                      (uu___249_14167.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14164)  in
              (uu____14157, r)  in
            FStar_Pervasives_Native.Some uu____14146
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14215 = lookup_qname env l  in
      match uu____14215 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14234 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14286 = try_lookup_bv env bv  in
      match uu____14286 with
      | FStar_Pervasives_Native.None  ->
          let uu____14301 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14301 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14316 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14317 =
            let uu____14318 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14318  in
          (uu____14316, uu____14317)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14339 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14339 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14405 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14405  in
          let uu____14406 =
            let uu____14415 =
              let uu____14420 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14420)  in
            (uu____14415, r1)  in
          FStar_Pervasives_Native.Some uu____14406
  
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
        let uu____14454 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14454 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14487,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14512 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14512  in
            let uu____14513 =
              let uu____14518 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14518, r1)  in
            FStar_Pervasives_Native.Some uu____14513
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14541 = try_lookup_lid env l  in
      match uu____14541 with
      | FStar_Pervasives_Native.None  ->
          let uu____14568 = name_not_found l  in
          let uu____14573 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14568 uu____14573
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___230_14613  ->
              match uu___230_14613 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14615 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14634 = lookup_qname env lid  in
      match uu____14634 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14643,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14646;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14648;
              FStar_Syntax_Syntax.sigattrs = uu____14649;_},FStar_Pervasives_Native.None
            ),uu____14650)
          ->
          let uu____14699 =
            let uu____14706 =
              let uu____14707 =
                let uu____14710 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____14710 t  in
              (uvs, uu____14707)  in
            (uu____14706, q)  in
          FStar_Pervasives_Native.Some uu____14699
      | uu____14723 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14744 = lookup_qname env lid  in
      match uu____14744 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14749,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14752;
              FStar_Syntax_Syntax.sigquals = uu____14753;
              FStar_Syntax_Syntax.sigmeta = uu____14754;
              FStar_Syntax_Syntax.sigattrs = uu____14755;_},FStar_Pervasives_Native.None
            ),uu____14756)
          ->
          let uu____14805 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14805 (uvs, t)
      | uu____14810 ->
          let uu____14811 = name_not_found lid  in
          let uu____14816 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14811 uu____14816
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14835 = lookup_qname env lid  in
      match uu____14835 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14840,uvs,t,uu____14843,uu____14844,uu____14845);
              FStar_Syntax_Syntax.sigrng = uu____14846;
              FStar_Syntax_Syntax.sigquals = uu____14847;
              FStar_Syntax_Syntax.sigmeta = uu____14848;
              FStar_Syntax_Syntax.sigattrs = uu____14849;_},FStar_Pervasives_Native.None
            ),uu____14850)
          ->
          let uu____14903 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____14903 (uvs, t)
      | uu____14908 ->
          let uu____14909 = name_not_found lid  in
          let uu____14914 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14909 uu____14914
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____14935 = lookup_qname env lid  in
      match uu____14935 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14942,uu____14943,uu____14944,uu____14945,uu____14946,dcs);
              FStar_Syntax_Syntax.sigrng = uu____14948;
              FStar_Syntax_Syntax.sigquals = uu____14949;
              FStar_Syntax_Syntax.sigmeta = uu____14950;
              FStar_Syntax_Syntax.sigattrs = uu____14951;_},uu____14952),uu____14953)
          -> (true, dcs)
      | uu____15014 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15027 = lookup_qname env lid  in
      match uu____15027 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15028,uu____15029,uu____15030,l,uu____15032,uu____15033);
              FStar_Syntax_Syntax.sigrng = uu____15034;
              FStar_Syntax_Syntax.sigquals = uu____15035;
              FStar_Syntax_Syntax.sigmeta = uu____15036;
              FStar_Syntax_Syntax.sigattrs = uu____15037;_},uu____15038),uu____15039)
          -> l
      | uu____15094 ->
          let uu____15095 =
            let uu____15096 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15096  in
          failwith uu____15095
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15145)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15196,lbs),uu____15198)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15220 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15220
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15252 -> FStar_Pervasives_Native.None)
        | uu____15257 -> FStar_Pervasives_Native.None
  
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
        let uu____15287 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15287
  
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
             (FStar_Util.Inl uu____15332,uu____15333) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____15381),uu____15382) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____15431 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____15448 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____15457 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____15472 ->
                  let uu____15479 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____15479
              | FStar_Syntax_Syntax.Sig_let ((uu____15480,lbs),uu____15482)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____15496 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____15496
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____15500 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____15507 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____15508 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____15515 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15516 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____15517 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15518 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____15531 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____15544 =
           let uu____15547 =
             lookup_qname env
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              in
           delta_depth_of_qninfo fv uu____15547  in
         match uu____15544 with
         | FStar_Pervasives_Native.None  ->
             let uu____15548 =
               let uu____15549 = FStar_Syntax_Print.fv_to_string fv  in
               FStar_Util.format1 "Delta depth not found for %s" uu____15549
                in
             failwith uu____15548
         | FStar_Pervasives_Native.Some d ->
             ((let uu____15552 =
                 (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                   (FStar_Options.debug_any ())
                  in
               if uu____15552
               then
                 let uu____15553 = FStar_Syntax_Print.fv_to_string fv  in
                 let uu____15554 =
                   FStar_Syntax_Print.delta_depth_to_string
                     fv.FStar_Syntax_Syntax.fv_delta
                    in
                 let uu____15555 = FStar_Syntax_Print.delta_depth_to_string d
                    in
                 FStar_Util.print3
                   "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                   uu____15553 uu____15554 uu____15555
               else ());
              d))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15575),uu____15576) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15625 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15646),uu____15647) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15696 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15717 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15717
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15736 = lookup_qname env ftv  in
      match uu____15736 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15740) ->
          let uu____15785 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15785 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15806,t),r) ->
               let uu____15821 =
                 let uu____15822 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15822 t  in
               FStar_Pervasives_Native.Some uu____15821)
      | uu____15823 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15834 = try_lookup_effect_lid env ftv  in
      match uu____15834 with
      | FStar_Pervasives_Native.None  ->
          let uu____15837 = name_not_found ftv  in
          let uu____15842 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15837 uu____15842
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
        let uu____15865 = lookup_qname env lid0  in
        match uu____15865 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15876);
                FStar_Syntax_Syntax.sigrng = uu____15877;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15879;
                FStar_Syntax_Syntax.sigattrs = uu____15880;_},FStar_Pervasives_Native.None
              ),uu____15881)
            ->
            let lid1 =
              let uu____15935 =
                let uu____15936 = FStar_Ident.range_of_lid lid  in
                let uu____15937 =
                  let uu____15938 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____15938  in
                FStar_Range.set_use_range uu____15936 uu____15937  in
              FStar_Ident.set_lid_range lid uu____15935  in
            let uu____15939 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___231_15943  ->
                      match uu___231_15943 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____15944 -> false))
               in
            if uu____15939
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15958 =
                      let uu____15959 =
                        let uu____15960 = get_range env  in
                        FStar_Range.string_of_range uu____15960  in
                      let uu____15961 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____15962 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15959 uu____15961 uu____15962
                       in
                    failwith uu____15958)
                  in
               match (binders, univs1) with
               | ([],uu____15979) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16004,uu____16005::uu____16006::uu____16007) ->
                   let uu____16028 =
                     let uu____16029 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____16030 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16029 uu____16030
                      in
                   failwith uu____16028
               | uu____16037 ->
                   let uu____16052 =
                     let uu____16057 =
                       let uu____16058 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____16058)  in
                     inst_tscheme_with uu____16057 insts  in
                   (match uu____16052 with
                    | (uu____16071,t) ->
                        let t1 =
                          let uu____16074 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16074 t  in
                        let uu____16075 =
                          let uu____16076 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16076.FStar_Syntax_Syntax.n  in
                        (match uu____16075 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16111 -> failwith "Impossible")))
        | uu____16118 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16141 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16141 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16154,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16161 = find1 l2  in
            (match uu____16161 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16168 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16168 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16172 = find1 l  in
            (match uu____16172 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16177 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16177
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16191 = lookup_qname env l1  in
      match uu____16191 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16194;
              FStar_Syntax_Syntax.sigrng = uu____16195;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16197;
              FStar_Syntax_Syntax.sigattrs = uu____16198;_},uu____16199),uu____16200)
          -> q
      | uu____16251 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16272 =
          let uu____16273 =
            let uu____16274 = FStar_Util.string_of_int i  in
            let uu____16275 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16274 uu____16275
             in
          failwith uu____16273  in
        let uu____16276 = lookup_datacon env lid  in
        match uu____16276 with
        | (uu____16281,t) ->
            let uu____16283 =
              let uu____16284 = FStar_Syntax_Subst.compress t  in
              uu____16284.FStar_Syntax_Syntax.n  in
            (match uu____16283 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16288) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16329 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16329
                      FStar_Pervasives_Native.fst)
             | uu____16340 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16351 = lookup_qname env l  in
      match uu____16351 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16352,uu____16353,uu____16354);
              FStar_Syntax_Syntax.sigrng = uu____16355;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16357;
              FStar_Syntax_Syntax.sigattrs = uu____16358;_},uu____16359),uu____16360)
          ->
          FStar_Util.for_some
            (fun uu___232_16413  ->
               match uu___232_16413 with
               | FStar_Syntax_Syntax.Projector uu____16414 -> true
               | uu____16419 -> false) quals
      | uu____16420 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16431 = lookup_qname env lid  in
      match uu____16431 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16432,uu____16433,uu____16434,uu____16435,uu____16436,uu____16437);
              FStar_Syntax_Syntax.sigrng = uu____16438;
              FStar_Syntax_Syntax.sigquals = uu____16439;
              FStar_Syntax_Syntax.sigmeta = uu____16440;
              FStar_Syntax_Syntax.sigattrs = uu____16441;_},uu____16442),uu____16443)
          -> true
      | uu____16498 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16509 = lookup_qname env lid  in
      match uu____16509 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16510,uu____16511,uu____16512,uu____16513,uu____16514,uu____16515);
              FStar_Syntax_Syntax.sigrng = uu____16516;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16518;
              FStar_Syntax_Syntax.sigattrs = uu____16519;_},uu____16520),uu____16521)
          ->
          FStar_Util.for_some
            (fun uu___233_16582  ->
               match uu___233_16582 with
               | FStar_Syntax_Syntax.RecordType uu____16583 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16592 -> true
               | uu____16601 -> false) quals
      | uu____16602 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16608,uu____16609);
            FStar_Syntax_Syntax.sigrng = uu____16610;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16612;
            FStar_Syntax_Syntax.sigattrs = uu____16613;_},uu____16614),uu____16615)
        ->
        FStar_Util.for_some
          (fun uu___234_16672  ->
             match uu___234_16672 with
             | FStar_Syntax_Syntax.Action uu____16673 -> true
             | uu____16674 -> false) quals
    | uu____16675 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16686 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16686
  
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
      let uu____16700 =
        let uu____16701 = FStar_Syntax_Util.un_uinst head1  in
        uu____16701.FStar_Syntax_Syntax.n  in
      match uu____16700 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16705 ->
               true
           | uu____16706 -> false)
      | uu____16707 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16718 = lookup_qname env l  in
      match uu____16718 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16720),uu____16721) ->
          FStar_Util.for_some
            (fun uu___235_16769  ->
               match uu___235_16769 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16770 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16771 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16842 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16858) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16875 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16882 ->
                 FStar_Pervasives_Native.Some true
             | uu____16899 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16900 =
        let uu____16903 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16903 mapper  in
      match uu____16900 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____16955 = lookup_qname env lid  in
      match uu____16955 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16958,uu____16959,tps,uu____16961,uu____16962,uu____16963);
              FStar_Syntax_Syntax.sigrng = uu____16964;
              FStar_Syntax_Syntax.sigquals = uu____16965;
              FStar_Syntax_Syntax.sigmeta = uu____16966;
              FStar_Syntax_Syntax.sigattrs = uu____16967;_},uu____16968),uu____16969)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____17034 -> FStar_Pervasives_Native.None
  
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
           (fun uu____17078  ->
              match uu____17078 with
              | (d,uu____17086) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17101 = effect_decl_opt env l  in
      match uu____17101 with
      | FStar_Pervasives_Native.None  ->
          let uu____17116 = name_not_found l  in
          let uu____17121 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17116 uu____17121
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17143  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17162  ->
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
        let uu____17193 = FStar_Ident.lid_equals l1 l2  in
        if uu____17193
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17201 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17201
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17209 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17262  ->
                        match uu____17262 with
                        | (m1,m2,uu____17275,uu____17276,uu____17277) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17209 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17294 =
                    let uu____17299 =
                      let uu____17300 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17301 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17300
                        uu____17301
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17299)
                     in
                  FStar_Errors.raise_error uu____17294 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17308,uu____17309,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17342 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17342
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
  'Auu____17358 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17358)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17387 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17413  ->
                match uu____17413 with
                | (d,uu____17419) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17387 with
      | FStar_Pervasives_Native.None  ->
          let uu____17430 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17430
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17443 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17443 with
           | (uu____17458,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17476)::(wp,uu____17478)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17534 -> failwith "Impossible"))
  
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
          let uu____17589 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17589
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17591 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17591
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
                  let uu____17599 = get_range env  in
                  let uu____17600 =
                    let uu____17607 =
                      let uu____17608 =
                        let uu____17625 =
                          let uu____17636 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17636]  in
                        (null_wp, uu____17625)  in
                      FStar_Syntax_Syntax.Tm_app uu____17608  in
                    FStar_Syntax_Syntax.mk uu____17607  in
                  uu____17600 FStar_Pervasives_Native.None uu____17599  in
                let uu____17676 =
                  let uu____17677 =
                    let uu____17688 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17688]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17677;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17676))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___250_17725 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___250_17725.order);
              joins = (uu___250_17725.joins)
            }  in
          let uu___251_17734 = env  in
          {
            solver = (uu___251_17734.solver);
            range = (uu___251_17734.range);
            curmodule = (uu___251_17734.curmodule);
            gamma = (uu___251_17734.gamma);
            gamma_sig = (uu___251_17734.gamma_sig);
            gamma_cache = (uu___251_17734.gamma_cache);
            modules = (uu___251_17734.modules);
            expected_typ = (uu___251_17734.expected_typ);
            sigtab = (uu___251_17734.sigtab);
            attrtab = (uu___251_17734.attrtab);
            is_pattern = (uu___251_17734.is_pattern);
            instantiate_imp = (uu___251_17734.instantiate_imp);
            effects;
            generalize = (uu___251_17734.generalize);
            letrecs = (uu___251_17734.letrecs);
            top_level = (uu___251_17734.top_level);
            check_uvars = (uu___251_17734.check_uvars);
            use_eq = (uu___251_17734.use_eq);
            is_iface = (uu___251_17734.is_iface);
            admit = (uu___251_17734.admit);
            lax = (uu___251_17734.lax);
            lax_universes = (uu___251_17734.lax_universes);
            phase1 = (uu___251_17734.phase1);
            failhard = (uu___251_17734.failhard);
            nosynth = (uu___251_17734.nosynth);
            uvar_subtyping = (uu___251_17734.uvar_subtyping);
            tc_term = (uu___251_17734.tc_term);
            type_of = (uu___251_17734.type_of);
            universe_of = (uu___251_17734.universe_of);
            check_type_of = (uu___251_17734.check_type_of);
            use_bv_sorts = (uu___251_17734.use_bv_sorts);
            qtbl_name_and_index = (uu___251_17734.qtbl_name_and_index);
            normalized_eff_names = (uu___251_17734.normalized_eff_names);
            proof_ns = (uu___251_17734.proof_ns);
            synth_hook = (uu___251_17734.synth_hook);
            splice = (uu___251_17734.splice);
            is_native_tactic = (uu___251_17734.is_native_tactic);
            identifier_info = (uu___251_17734.identifier_info);
            tc_hooks = (uu___251_17734.tc_hooks);
            dsenv = (uu___251_17734.dsenv);
            nbe = (uu___251_17734.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17764 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17764  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____17922 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____17923 = l1 u t wp e  in
                                l2 u t uu____17922 uu____17923))
                | uu____17924 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____17996 = inst_tscheme_with lift_t [u]  in
            match uu____17996 with
            | (uu____18003,lift_t1) ->
                let uu____18005 =
                  let uu____18012 =
                    let uu____18013 =
                      let uu____18030 =
                        let uu____18041 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18050 =
                          let uu____18061 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18061]  in
                        uu____18041 :: uu____18050  in
                      (lift_t1, uu____18030)  in
                    FStar_Syntax_Syntax.Tm_app uu____18013  in
                  FStar_Syntax_Syntax.mk uu____18012  in
                uu____18005 FStar_Pervasives_Native.None
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
            let uu____18173 = inst_tscheme_with lift_t [u]  in
            match uu____18173 with
            | (uu____18180,lift_t1) ->
                let uu____18182 =
                  let uu____18189 =
                    let uu____18190 =
                      let uu____18207 =
                        let uu____18218 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18227 =
                          let uu____18238 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18247 =
                            let uu____18258 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18258]  in
                          uu____18238 :: uu____18247  in
                        uu____18218 :: uu____18227  in
                      (lift_t1, uu____18207)  in
                    FStar_Syntax_Syntax.Tm_app uu____18190  in
                  FStar_Syntax_Syntax.mk uu____18189  in
                uu____18182 FStar_Pervasives_Native.None
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
              let uu____18360 =
                let uu____18361 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18361
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18360  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18365 =
              let uu____18366 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18366  in
            let uu____18367 =
              let uu____18368 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18394 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18394)
                 in
              FStar_Util.dflt "none" uu____18368  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18365
              uu____18367
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18420  ->
                    match uu____18420 with
                    | (e,uu____18428) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18451 =
            match uu____18451 with
            | (i,j) ->
                let uu____18462 = FStar_Ident.lid_equals i j  in
                if uu____18462
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
              let uu____18494 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18504 = FStar_Ident.lid_equals i k  in
                        if uu____18504
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18515 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18515
                                  then []
                                  else
                                    (let uu____18519 =
                                       let uu____18528 =
                                         find_edge order1 (i, k)  in
                                       let uu____18531 =
                                         find_edge order1 (k, j)  in
                                       (uu____18528, uu____18531)  in
                                     match uu____18519 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18546 =
                                           compose_edges e1 e2  in
                                         [uu____18546]
                                     | uu____18547 -> [])))))
                 in
              FStar_List.append order1 uu____18494  in
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
                   let uu____18577 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18579 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18579
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18577
                   then
                     let uu____18584 =
                       let uu____18589 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18589)
                        in
                     let uu____18590 = get_range env  in
                     FStar_Errors.raise_error uu____18584 uu____18590
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18667 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18667
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18716 =
                                              let uu____18725 =
                                                find_edge order2 (i, k)  in
                                              let uu____18728 =
                                                find_edge order2 (j, k)  in
                                              (uu____18725, uu____18728)  in
                                            match uu____18716 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18770,uu____18771)
                                                     ->
                                                     let uu____18778 =
                                                       let uu____18783 =
                                                         let uu____18784 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18784
                                                          in
                                                       let uu____18787 =
                                                         let uu____18788 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18788
                                                          in
                                                       (uu____18783,
                                                         uu____18787)
                                                        in
                                                     (match uu____18778 with
                                                      | (true ,true ) ->
                                                          let uu____18799 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18799
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
                                            | uu____18824 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___252_18897 = env.effects  in
              { decls = (uu___252_18897.decls); order = order2; joins }  in
            let uu___253_18898 = env  in
            {
              solver = (uu___253_18898.solver);
              range = (uu___253_18898.range);
              curmodule = (uu___253_18898.curmodule);
              gamma = (uu___253_18898.gamma);
              gamma_sig = (uu___253_18898.gamma_sig);
              gamma_cache = (uu___253_18898.gamma_cache);
              modules = (uu___253_18898.modules);
              expected_typ = (uu___253_18898.expected_typ);
              sigtab = (uu___253_18898.sigtab);
              attrtab = (uu___253_18898.attrtab);
              is_pattern = (uu___253_18898.is_pattern);
              instantiate_imp = (uu___253_18898.instantiate_imp);
              effects;
              generalize = (uu___253_18898.generalize);
              letrecs = (uu___253_18898.letrecs);
              top_level = (uu___253_18898.top_level);
              check_uvars = (uu___253_18898.check_uvars);
              use_eq = (uu___253_18898.use_eq);
              is_iface = (uu___253_18898.is_iface);
              admit = (uu___253_18898.admit);
              lax = (uu___253_18898.lax);
              lax_universes = (uu___253_18898.lax_universes);
              phase1 = (uu___253_18898.phase1);
              failhard = (uu___253_18898.failhard);
              nosynth = (uu___253_18898.nosynth);
              uvar_subtyping = (uu___253_18898.uvar_subtyping);
              tc_term = (uu___253_18898.tc_term);
              type_of = (uu___253_18898.type_of);
              universe_of = (uu___253_18898.universe_of);
              check_type_of = (uu___253_18898.check_type_of);
              use_bv_sorts = (uu___253_18898.use_bv_sorts);
              qtbl_name_and_index = (uu___253_18898.qtbl_name_and_index);
              normalized_eff_names = (uu___253_18898.normalized_eff_names);
              proof_ns = (uu___253_18898.proof_ns);
              synth_hook = (uu___253_18898.synth_hook);
              splice = (uu___253_18898.splice);
              is_native_tactic = (uu___253_18898.is_native_tactic);
              identifier_info = (uu___253_18898.identifier_info);
              tc_hooks = (uu___253_18898.tc_hooks);
              dsenv = (uu___253_18898.dsenv);
              nbe = (uu___253_18898.nbe)
            }))
      | uu____18899 -> env
  
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
        | uu____18927 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____18939 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____18939 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____18956 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____18956 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18978 =
                     let uu____18983 =
                       let uu____18984 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____18991 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____19000 =
                         let uu____19001 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____19001  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18984 uu____18991 uu____19000
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18983)
                      in
                   FStar_Errors.raise_error uu____18978
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19006 =
                     let uu____19017 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____19017 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____19054  ->
                        fun uu____19055  ->
                          match (uu____19054, uu____19055) with
                          | ((x,uu____19085),(t,uu____19087)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19006
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19118 =
                     let uu___254_19119 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___254_19119.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___254_19119.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___254_19119.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___254_19119.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19118
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____19130 .
    'Auu____19130 ->
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
          let uu____19160 = effect_decl_opt env effect_name  in
          match uu____19160 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____19199 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19222 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____19259 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____19259
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____19260 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19260
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____19274 =
                     let uu____19277 = get_range env  in
                     let uu____19278 =
                       let uu____19285 =
                         let uu____19286 =
                           let uu____19303 =
                             let uu____19314 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____19314; wp]  in
                           (repr, uu____19303)  in
                         FStar_Syntax_Syntax.Tm_app uu____19286  in
                       FStar_Syntax_Syntax.mk uu____19285  in
                     uu____19278 FStar_Pervasives_Native.None uu____19277  in
                   FStar_Pervasives_Native.Some uu____19274)
  
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
      | uu____19429 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19440 =
        let uu____19441 = FStar_Syntax_Subst.compress t  in
        uu____19441.FStar_Syntax_Syntax.n  in
      match uu____19440 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19444,c) ->
          is_reifiable_comp env c
      | uu____19466 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____19484 =
           let uu____19485 = is_reifiable_effect env l  in
           Prims.op_Negation uu____19485  in
         if uu____19484
         then
           let uu____19486 =
             let uu____19491 =
               let uu____19492 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19492
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19491)  in
           let uu____19493 = get_range env  in
           FStar_Errors.raise_error uu____19486 uu____19493
         else ());
        (let uu____19495 = effect_repr_aux true env c u_c  in
         match uu____19495 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___255_19527 = env  in
        {
          solver = (uu___255_19527.solver);
          range = (uu___255_19527.range);
          curmodule = (uu___255_19527.curmodule);
          gamma = (uu___255_19527.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___255_19527.gamma_cache);
          modules = (uu___255_19527.modules);
          expected_typ = (uu___255_19527.expected_typ);
          sigtab = (uu___255_19527.sigtab);
          attrtab = (uu___255_19527.attrtab);
          is_pattern = (uu___255_19527.is_pattern);
          instantiate_imp = (uu___255_19527.instantiate_imp);
          effects = (uu___255_19527.effects);
          generalize = (uu___255_19527.generalize);
          letrecs = (uu___255_19527.letrecs);
          top_level = (uu___255_19527.top_level);
          check_uvars = (uu___255_19527.check_uvars);
          use_eq = (uu___255_19527.use_eq);
          is_iface = (uu___255_19527.is_iface);
          admit = (uu___255_19527.admit);
          lax = (uu___255_19527.lax);
          lax_universes = (uu___255_19527.lax_universes);
          phase1 = (uu___255_19527.phase1);
          failhard = (uu___255_19527.failhard);
          nosynth = (uu___255_19527.nosynth);
          uvar_subtyping = (uu___255_19527.uvar_subtyping);
          tc_term = (uu___255_19527.tc_term);
          type_of = (uu___255_19527.type_of);
          universe_of = (uu___255_19527.universe_of);
          check_type_of = (uu___255_19527.check_type_of);
          use_bv_sorts = (uu___255_19527.use_bv_sorts);
          qtbl_name_and_index = (uu___255_19527.qtbl_name_and_index);
          normalized_eff_names = (uu___255_19527.normalized_eff_names);
          proof_ns = (uu___255_19527.proof_ns);
          synth_hook = (uu___255_19527.synth_hook);
          splice = (uu___255_19527.splice);
          is_native_tactic = (uu___255_19527.is_native_tactic);
          identifier_info = (uu___255_19527.identifier_info);
          tc_hooks = (uu___255_19527.tc_hooks);
          dsenv = (uu___255_19527.dsenv);
          nbe = (uu___255_19527.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___256_19540 = env  in
      {
        solver = (uu___256_19540.solver);
        range = (uu___256_19540.range);
        curmodule = (uu___256_19540.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___256_19540.gamma_sig);
        gamma_cache = (uu___256_19540.gamma_cache);
        modules = (uu___256_19540.modules);
        expected_typ = (uu___256_19540.expected_typ);
        sigtab = (uu___256_19540.sigtab);
        attrtab = (uu___256_19540.attrtab);
        is_pattern = (uu___256_19540.is_pattern);
        instantiate_imp = (uu___256_19540.instantiate_imp);
        effects = (uu___256_19540.effects);
        generalize = (uu___256_19540.generalize);
        letrecs = (uu___256_19540.letrecs);
        top_level = (uu___256_19540.top_level);
        check_uvars = (uu___256_19540.check_uvars);
        use_eq = (uu___256_19540.use_eq);
        is_iface = (uu___256_19540.is_iface);
        admit = (uu___256_19540.admit);
        lax = (uu___256_19540.lax);
        lax_universes = (uu___256_19540.lax_universes);
        phase1 = (uu___256_19540.phase1);
        failhard = (uu___256_19540.failhard);
        nosynth = (uu___256_19540.nosynth);
        uvar_subtyping = (uu___256_19540.uvar_subtyping);
        tc_term = (uu___256_19540.tc_term);
        type_of = (uu___256_19540.type_of);
        universe_of = (uu___256_19540.universe_of);
        check_type_of = (uu___256_19540.check_type_of);
        use_bv_sorts = (uu___256_19540.use_bv_sorts);
        qtbl_name_and_index = (uu___256_19540.qtbl_name_and_index);
        normalized_eff_names = (uu___256_19540.normalized_eff_names);
        proof_ns = (uu___256_19540.proof_ns);
        synth_hook = (uu___256_19540.synth_hook);
        splice = (uu___256_19540.splice);
        is_native_tactic = (uu___256_19540.is_native_tactic);
        identifier_info = (uu___256_19540.identifier_info);
        tc_hooks = (uu___256_19540.tc_hooks);
        dsenv = (uu___256_19540.dsenv);
        nbe = (uu___256_19540.nbe)
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
            (let uu___257_19595 = env  in
             {
               solver = (uu___257_19595.solver);
               range = (uu___257_19595.range);
               curmodule = (uu___257_19595.curmodule);
               gamma = rest;
               gamma_sig = (uu___257_19595.gamma_sig);
               gamma_cache = (uu___257_19595.gamma_cache);
               modules = (uu___257_19595.modules);
               expected_typ = (uu___257_19595.expected_typ);
               sigtab = (uu___257_19595.sigtab);
               attrtab = (uu___257_19595.attrtab);
               is_pattern = (uu___257_19595.is_pattern);
               instantiate_imp = (uu___257_19595.instantiate_imp);
               effects = (uu___257_19595.effects);
               generalize = (uu___257_19595.generalize);
               letrecs = (uu___257_19595.letrecs);
               top_level = (uu___257_19595.top_level);
               check_uvars = (uu___257_19595.check_uvars);
               use_eq = (uu___257_19595.use_eq);
               is_iface = (uu___257_19595.is_iface);
               admit = (uu___257_19595.admit);
               lax = (uu___257_19595.lax);
               lax_universes = (uu___257_19595.lax_universes);
               phase1 = (uu___257_19595.phase1);
               failhard = (uu___257_19595.failhard);
               nosynth = (uu___257_19595.nosynth);
               uvar_subtyping = (uu___257_19595.uvar_subtyping);
               tc_term = (uu___257_19595.tc_term);
               type_of = (uu___257_19595.type_of);
               universe_of = (uu___257_19595.universe_of);
               check_type_of = (uu___257_19595.check_type_of);
               use_bv_sorts = (uu___257_19595.use_bv_sorts);
               qtbl_name_and_index = (uu___257_19595.qtbl_name_and_index);
               normalized_eff_names = (uu___257_19595.normalized_eff_names);
               proof_ns = (uu___257_19595.proof_ns);
               synth_hook = (uu___257_19595.synth_hook);
               splice = (uu___257_19595.splice);
               is_native_tactic = (uu___257_19595.is_native_tactic);
               identifier_info = (uu___257_19595.identifier_info);
               tc_hooks = (uu___257_19595.tc_hooks);
               dsenv = (uu___257_19595.dsenv);
               nbe = (uu___257_19595.nbe)
             }))
    | uu____19596 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19624  ->
             match uu____19624 with | (x,uu____19632) -> push_bv env1 x) env
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
            let uu___258_19666 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___258_19666.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___258_19666.FStar_Syntax_Syntax.index);
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
      (let uu___259_19706 = env  in
       {
         solver = (uu___259_19706.solver);
         range = (uu___259_19706.range);
         curmodule = (uu___259_19706.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___259_19706.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___259_19706.sigtab);
         attrtab = (uu___259_19706.attrtab);
         is_pattern = (uu___259_19706.is_pattern);
         instantiate_imp = (uu___259_19706.instantiate_imp);
         effects = (uu___259_19706.effects);
         generalize = (uu___259_19706.generalize);
         letrecs = (uu___259_19706.letrecs);
         top_level = (uu___259_19706.top_level);
         check_uvars = (uu___259_19706.check_uvars);
         use_eq = (uu___259_19706.use_eq);
         is_iface = (uu___259_19706.is_iface);
         admit = (uu___259_19706.admit);
         lax = (uu___259_19706.lax);
         lax_universes = (uu___259_19706.lax_universes);
         phase1 = (uu___259_19706.phase1);
         failhard = (uu___259_19706.failhard);
         nosynth = (uu___259_19706.nosynth);
         uvar_subtyping = (uu___259_19706.uvar_subtyping);
         tc_term = (uu___259_19706.tc_term);
         type_of = (uu___259_19706.type_of);
         universe_of = (uu___259_19706.universe_of);
         check_type_of = (uu___259_19706.check_type_of);
         use_bv_sorts = (uu___259_19706.use_bv_sorts);
         qtbl_name_and_index = (uu___259_19706.qtbl_name_and_index);
         normalized_eff_names = (uu___259_19706.normalized_eff_names);
         proof_ns = (uu___259_19706.proof_ns);
         synth_hook = (uu___259_19706.synth_hook);
         splice = (uu___259_19706.splice);
         is_native_tactic = (uu___259_19706.is_native_tactic);
         identifier_info = (uu___259_19706.identifier_info);
         tc_hooks = (uu___259_19706.tc_hooks);
         dsenv = (uu___259_19706.dsenv);
         nbe = (uu___259_19706.nbe)
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
        let uu____19748 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19748 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19776 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19776)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___260_19791 = env  in
      {
        solver = (uu___260_19791.solver);
        range = (uu___260_19791.range);
        curmodule = (uu___260_19791.curmodule);
        gamma = (uu___260_19791.gamma);
        gamma_sig = (uu___260_19791.gamma_sig);
        gamma_cache = (uu___260_19791.gamma_cache);
        modules = (uu___260_19791.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___260_19791.sigtab);
        attrtab = (uu___260_19791.attrtab);
        is_pattern = (uu___260_19791.is_pattern);
        instantiate_imp = (uu___260_19791.instantiate_imp);
        effects = (uu___260_19791.effects);
        generalize = (uu___260_19791.generalize);
        letrecs = (uu___260_19791.letrecs);
        top_level = (uu___260_19791.top_level);
        check_uvars = (uu___260_19791.check_uvars);
        use_eq = false;
        is_iface = (uu___260_19791.is_iface);
        admit = (uu___260_19791.admit);
        lax = (uu___260_19791.lax);
        lax_universes = (uu___260_19791.lax_universes);
        phase1 = (uu___260_19791.phase1);
        failhard = (uu___260_19791.failhard);
        nosynth = (uu___260_19791.nosynth);
        uvar_subtyping = (uu___260_19791.uvar_subtyping);
        tc_term = (uu___260_19791.tc_term);
        type_of = (uu___260_19791.type_of);
        universe_of = (uu___260_19791.universe_of);
        check_type_of = (uu___260_19791.check_type_of);
        use_bv_sorts = (uu___260_19791.use_bv_sorts);
        qtbl_name_and_index = (uu___260_19791.qtbl_name_and_index);
        normalized_eff_names = (uu___260_19791.normalized_eff_names);
        proof_ns = (uu___260_19791.proof_ns);
        synth_hook = (uu___260_19791.synth_hook);
        splice = (uu___260_19791.splice);
        is_native_tactic = (uu___260_19791.is_native_tactic);
        identifier_info = (uu___260_19791.identifier_info);
        tc_hooks = (uu___260_19791.tc_hooks);
        dsenv = (uu___260_19791.dsenv);
        nbe = (uu___260_19791.nbe)
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
    let uu____19819 = expected_typ env_  in
    ((let uu___261_19825 = env_  in
      {
        solver = (uu___261_19825.solver);
        range = (uu___261_19825.range);
        curmodule = (uu___261_19825.curmodule);
        gamma = (uu___261_19825.gamma);
        gamma_sig = (uu___261_19825.gamma_sig);
        gamma_cache = (uu___261_19825.gamma_cache);
        modules = (uu___261_19825.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___261_19825.sigtab);
        attrtab = (uu___261_19825.attrtab);
        is_pattern = (uu___261_19825.is_pattern);
        instantiate_imp = (uu___261_19825.instantiate_imp);
        effects = (uu___261_19825.effects);
        generalize = (uu___261_19825.generalize);
        letrecs = (uu___261_19825.letrecs);
        top_level = (uu___261_19825.top_level);
        check_uvars = (uu___261_19825.check_uvars);
        use_eq = false;
        is_iface = (uu___261_19825.is_iface);
        admit = (uu___261_19825.admit);
        lax = (uu___261_19825.lax);
        lax_universes = (uu___261_19825.lax_universes);
        phase1 = (uu___261_19825.phase1);
        failhard = (uu___261_19825.failhard);
        nosynth = (uu___261_19825.nosynth);
        uvar_subtyping = (uu___261_19825.uvar_subtyping);
        tc_term = (uu___261_19825.tc_term);
        type_of = (uu___261_19825.type_of);
        universe_of = (uu___261_19825.universe_of);
        check_type_of = (uu___261_19825.check_type_of);
        use_bv_sorts = (uu___261_19825.use_bv_sorts);
        qtbl_name_and_index = (uu___261_19825.qtbl_name_and_index);
        normalized_eff_names = (uu___261_19825.normalized_eff_names);
        proof_ns = (uu___261_19825.proof_ns);
        synth_hook = (uu___261_19825.synth_hook);
        splice = (uu___261_19825.splice);
        is_native_tactic = (uu___261_19825.is_native_tactic);
        identifier_info = (uu___261_19825.identifier_info);
        tc_hooks = (uu___261_19825.tc_hooks);
        dsenv = (uu___261_19825.dsenv);
        nbe = (uu___261_19825.nbe)
      }), uu____19819)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19835 =
      let uu____19838 = FStar_Ident.id_of_text ""  in [uu____19838]  in
    FStar_Ident.lid_of_ids uu____19835  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19844 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19844
        then
          let uu____19847 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19847 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___262_19874 = env  in
       {
         solver = (uu___262_19874.solver);
         range = (uu___262_19874.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___262_19874.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___262_19874.expected_typ);
         sigtab = (uu___262_19874.sigtab);
         attrtab = (uu___262_19874.attrtab);
         is_pattern = (uu___262_19874.is_pattern);
         instantiate_imp = (uu___262_19874.instantiate_imp);
         effects = (uu___262_19874.effects);
         generalize = (uu___262_19874.generalize);
         letrecs = (uu___262_19874.letrecs);
         top_level = (uu___262_19874.top_level);
         check_uvars = (uu___262_19874.check_uvars);
         use_eq = (uu___262_19874.use_eq);
         is_iface = (uu___262_19874.is_iface);
         admit = (uu___262_19874.admit);
         lax = (uu___262_19874.lax);
         lax_universes = (uu___262_19874.lax_universes);
         phase1 = (uu___262_19874.phase1);
         failhard = (uu___262_19874.failhard);
         nosynth = (uu___262_19874.nosynth);
         uvar_subtyping = (uu___262_19874.uvar_subtyping);
         tc_term = (uu___262_19874.tc_term);
         type_of = (uu___262_19874.type_of);
         universe_of = (uu___262_19874.universe_of);
         check_type_of = (uu___262_19874.check_type_of);
         use_bv_sorts = (uu___262_19874.use_bv_sorts);
         qtbl_name_and_index = (uu___262_19874.qtbl_name_and_index);
         normalized_eff_names = (uu___262_19874.normalized_eff_names);
         proof_ns = (uu___262_19874.proof_ns);
         synth_hook = (uu___262_19874.synth_hook);
         splice = (uu___262_19874.splice);
         is_native_tactic = (uu___262_19874.is_native_tactic);
         identifier_info = (uu___262_19874.identifier_info);
         tc_hooks = (uu___262_19874.tc_hooks);
         dsenv = (uu___262_19874.dsenv);
         nbe = (uu___262_19874.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19925)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____19929,(uu____19930,t)))::tl1
          ->
          let uu____19951 =
            let uu____19954 = FStar_Syntax_Free.uvars t  in
            ext out uu____19954  in
          aux uu____19951 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19957;
            FStar_Syntax_Syntax.index = uu____19958;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19965 =
            let uu____19968 = FStar_Syntax_Free.uvars t  in
            ext out uu____19968  in
          aux uu____19965 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20025)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20029,(uu____20030,t)))::tl1
          ->
          let uu____20051 =
            let uu____20054 = FStar_Syntax_Free.univs t  in
            ext out uu____20054  in
          aux uu____20051 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20057;
            FStar_Syntax_Syntax.index = uu____20058;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20065 =
            let uu____20068 = FStar_Syntax_Free.univs t  in
            ext out uu____20068  in
          aux uu____20065 tl1
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
          let uu____20129 = FStar_Util.set_add uname out  in
          aux uu____20129 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20132,(uu____20133,t)))::tl1
          ->
          let uu____20154 =
            let uu____20157 = FStar_Syntax_Free.univnames t  in
            ext out uu____20157  in
          aux uu____20154 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20160;
            FStar_Syntax_Syntax.index = uu____20161;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20168 =
            let uu____20171 = FStar_Syntax_Free.univnames t  in
            ext out uu____20171  in
          aux uu____20168 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___236_20191  ->
            match uu___236_20191 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20195 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20208 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20218 =
      let uu____20227 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20227
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20218 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20271 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___237_20281  ->
              match uu___237_20281 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20283 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20283
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20286) ->
                  let uu____20303 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20303))
       in
    FStar_All.pipe_right uu____20271 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___238_20310  ->
    match uu___238_20310 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20312 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20312
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20332  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20374) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20393,uu____20394) -> false  in
      let uu____20403 =
        FStar_List.tryFind
          (fun uu____20421  ->
             match uu____20421 with | (p,uu____20429) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20403 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20440,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20462 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20462
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___263_20480 = e  in
        {
          solver = (uu___263_20480.solver);
          range = (uu___263_20480.range);
          curmodule = (uu___263_20480.curmodule);
          gamma = (uu___263_20480.gamma);
          gamma_sig = (uu___263_20480.gamma_sig);
          gamma_cache = (uu___263_20480.gamma_cache);
          modules = (uu___263_20480.modules);
          expected_typ = (uu___263_20480.expected_typ);
          sigtab = (uu___263_20480.sigtab);
          attrtab = (uu___263_20480.attrtab);
          is_pattern = (uu___263_20480.is_pattern);
          instantiate_imp = (uu___263_20480.instantiate_imp);
          effects = (uu___263_20480.effects);
          generalize = (uu___263_20480.generalize);
          letrecs = (uu___263_20480.letrecs);
          top_level = (uu___263_20480.top_level);
          check_uvars = (uu___263_20480.check_uvars);
          use_eq = (uu___263_20480.use_eq);
          is_iface = (uu___263_20480.is_iface);
          admit = (uu___263_20480.admit);
          lax = (uu___263_20480.lax);
          lax_universes = (uu___263_20480.lax_universes);
          phase1 = (uu___263_20480.phase1);
          failhard = (uu___263_20480.failhard);
          nosynth = (uu___263_20480.nosynth);
          uvar_subtyping = (uu___263_20480.uvar_subtyping);
          tc_term = (uu___263_20480.tc_term);
          type_of = (uu___263_20480.type_of);
          universe_of = (uu___263_20480.universe_of);
          check_type_of = (uu___263_20480.check_type_of);
          use_bv_sorts = (uu___263_20480.use_bv_sorts);
          qtbl_name_and_index = (uu___263_20480.qtbl_name_and_index);
          normalized_eff_names = (uu___263_20480.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___263_20480.synth_hook);
          splice = (uu___263_20480.splice);
          is_native_tactic = (uu___263_20480.is_native_tactic);
          identifier_info = (uu___263_20480.identifier_info);
          tc_hooks = (uu___263_20480.tc_hooks);
          dsenv = (uu___263_20480.dsenv);
          nbe = (uu___263_20480.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___264_20520 = e  in
      {
        solver = (uu___264_20520.solver);
        range = (uu___264_20520.range);
        curmodule = (uu___264_20520.curmodule);
        gamma = (uu___264_20520.gamma);
        gamma_sig = (uu___264_20520.gamma_sig);
        gamma_cache = (uu___264_20520.gamma_cache);
        modules = (uu___264_20520.modules);
        expected_typ = (uu___264_20520.expected_typ);
        sigtab = (uu___264_20520.sigtab);
        attrtab = (uu___264_20520.attrtab);
        is_pattern = (uu___264_20520.is_pattern);
        instantiate_imp = (uu___264_20520.instantiate_imp);
        effects = (uu___264_20520.effects);
        generalize = (uu___264_20520.generalize);
        letrecs = (uu___264_20520.letrecs);
        top_level = (uu___264_20520.top_level);
        check_uvars = (uu___264_20520.check_uvars);
        use_eq = (uu___264_20520.use_eq);
        is_iface = (uu___264_20520.is_iface);
        admit = (uu___264_20520.admit);
        lax = (uu___264_20520.lax);
        lax_universes = (uu___264_20520.lax_universes);
        phase1 = (uu___264_20520.phase1);
        failhard = (uu___264_20520.failhard);
        nosynth = (uu___264_20520.nosynth);
        uvar_subtyping = (uu___264_20520.uvar_subtyping);
        tc_term = (uu___264_20520.tc_term);
        type_of = (uu___264_20520.type_of);
        universe_of = (uu___264_20520.universe_of);
        check_type_of = (uu___264_20520.check_type_of);
        use_bv_sorts = (uu___264_20520.use_bv_sorts);
        qtbl_name_and_index = (uu___264_20520.qtbl_name_and_index);
        normalized_eff_names = (uu___264_20520.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___264_20520.synth_hook);
        splice = (uu___264_20520.splice);
        is_native_tactic = (uu___264_20520.is_native_tactic);
        identifier_info = (uu___264_20520.identifier_info);
        tc_hooks = (uu___264_20520.tc_hooks);
        dsenv = (uu___264_20520.dsenv);
        nbe = (uu___264_20520.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20535 = FStar_Syntax_Free.names t  in
      let uu____20538 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20535 uu____20538
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20559 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20559
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20567 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20567
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20584 =
      match uu____20584 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20594 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20594)
       in
    let uu____20596 =
      let uu____20599 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20599 FStar_List.rev  in
    FStar_All.pipe_right uu____20596 (FStar_String.concat " ")
  
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
                  (let uu____20652 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20652 with
                   | FStar_Pervasives_Native.Some uu____20655 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20656 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20662;
        univ_ineqs = uu____20663; implicits = uu____20664;_} -> true
    | uu____20675 -> false
  
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
          let uu___265_20702 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___265_20702.deferred);
            univ_ineqs = (uu___265_20702.univ_ineqs);
            implicits = (uu___265_20702.implicits)
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
          let uu____20737 = FStar_Options.defensive ()  in
          if uu____20737
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20741 =
              let uu____20742 =
                let uu____20743 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20743  in
              Prims.op_Negation uu____20742  in
            (if uu____20741
             then
               let uu____20748 =
                 let uu____20753 =
                   let uu____20754 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20755 =
                     let uu____20756 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20756
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20754 uu____20755
                    in
                 (FStar_Errors.Warning_Defensive, uu____20753)  in
               FStar_Errors.log_issue rng uu____20748
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
          let uu____20787 =
            let uu____20788 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20788  in
          if uu____20787
          then ()
          else
            (let uu____20790 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20790 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20813 =
            let uu____20814 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20814  in
          if uu____20813
          then ()
          else
            (let uu____20816 = bound_vars e  in
             def_check_closed_in rng msg uu____20816 t)
  
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
          let uu___266_20851 = g  in
          let uu____20852 =
            let uu____20853 =
              let uu____20854 =
                let uu____20861 =
                  let uu____20862 =
                    let uu____20879 =
                      let uu____20890 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20890]  in
                    (f, uu____20879)  in
                  FStar_Syntax_Syntax.Tm_app uu____20862  in
                FStar_Syntax_Syntax.mk uu____20861  in
              uu____20854 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20853
             in
          {
            guard_f = uu____20852;
            deferred = (uu___266_20851.deferred);
            univ_ineqs = (uu___266_20851.univ_ineqs);
            implicits = (uu___266_20851.implicits)
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
          let uu___267_20946 = g  in
          let uu____20947 =
            let uu____20948 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20948  in
          {
            guard_f = uu____20947;
            deferred = (uu___267_20946.deferred);
            univ_ineqs = (uu___267_20946.univ_ineqs);
            implicits = (uu___267_20946.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___268_20964 = g  in
          let uu____20965 =
            let uu____20966 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____20966  in
          {
            guard_f = uu____20965;
            deferred = (uu___268_20964.deferred);
            univ_ineqs = (uu___268_20964.univ_ineqs);
            implicits = (uu___268_20964.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___269_20968 = g  in
          let uu____20969 =
            let uu____20970 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____20970  in
          {
            guard_f = uu____20969;
            deferred = (uu___269_20968.deferred);
            univ_ineqs = (uu___269_20968.univ_ineqs);
            implicits = (uu___269_20968.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20976 ->
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
          let uu____20991 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____20991
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____20997 =
      let uu____20998 = FStar_Syntax_Util.unmeta t  in
      uu____20998.FStar_Syntax_Syntax.n  in
    match uu____20997 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21002 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____21043 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____21043;
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
                       let uu____21133 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21133
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___270_21137 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___270_21137.deferred);
              univ_ineqs = (uu___270_21137.univ_ineqs);
              implicits = (uu___270_21137.implicits)
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
               let uu____21170 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21170
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
            let uu___271_21193 = g  in
            let uu____21194 =
              let uu____21195 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21195  in
            {
              guard_f = uu____21194;
              deferred = (uu___271_21193.deferred);
              univ_ineqs = (uu___271_21193.univ_ineqs);
              implicits = (uu___271_21193.implicits)
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
            let uu____21233 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21233 with
            | FStar_Pervasives_Native.Some
                (uu____21258::(tm,uu____21260)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21324 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21342 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21342;
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
                    let uu___272_21377 = trivial_guard  in
                    {
                      guard_f = (uu___272_21377.guard_f);
                      deferred = (uu___272_21377.deferred);
                      univ_ineqs = (uu___272_21377.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21394  -> ());
    push = (fun uu____21396  -> ());
    pop = (fun uu____21398  -> ());
    snapshot =
      (fun uu____21400  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21409  -> fun uu____21410  -> ());
    encode_modul = (fun uu____21421  -> fun uu____21422  -> ());
    encode_sig = (fun uu____21425  -> fun uu____21426  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21432 =
             let uu____21439 = FStar_Options.peek ()  in (e, g, uu____21439)
              in
           [uu____21432]);
    solve = (fun uu____21455  -> fun uu____21456  -> fun uu____21457  -> ());
    finish = (fun uu____21463  -> ());
    refresh = (fun uu____21465  -> ())
  } 