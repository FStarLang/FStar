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
  | NoDeltaSteps
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth
  | UnfoldOnly of FStar_Ident.lid Prims.list
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
  | Unascribe[@@deriving show]
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldAttr: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
let __proj__UnfoldAttr__item___0: step -> FStar_Syntax_Syntax.attribute =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
let uu___is_Unascribe: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
type steps = step Prims.list[@@deriving show]
type psc =
  {
  psc_range: FStar_Range.range;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst:
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____188  -> []) }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun psc  -> psc.psc_subst ()
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  requires_binder_substitution: Prims.bool;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____389 -> false
let __proj__Clos__item___0:
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____491 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____502 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___75_521  ->
    match uu___75_521 with
    | Clos (uu____522,t,uu____524,uu____525) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____570 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;
  strong: Prims.bool;
  memoize_lazy: Prims.bool;
  normalize_pure_lets: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
let __proj__Mkcfg__item__memoize_lazy: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
let __proj__Mkcfg__item__normalize_pure_lets: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____850 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____886 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____922 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____991 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1033 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1089 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1129 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1161 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1197 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1213 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1238 .
    'Auu____1238 ->
      FStar_Range.range -> 'Auu____1238 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1292 = FStar_ST.op_Bang r in
          match uu____1292 with
          | FStar_Pervasives_Native.Some uu____1340 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1394 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1394 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___76_1401  ->
    match uu___76_1401 with
    | Arg (c,uu____1403,uu____1404) ->
        let uu____1405 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1405
    | MemoLazy uu____1406 -> "MemoLazy"
    | Abs (uu____1413,bs,uu____1415,uu____1416,uu____1417) ->
        let uu____1422 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1422
    | UnivArgs uu____1427 -> "UnivArgs"
    | Match uu____1434 -> "Match"
    | App (uu____1441,t,uu____1443,uu____1444) ->
        let uu____1445 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1445
    | Meta (m,uu____1447) -> "Meta"
    | Let uu____1448 -> "Let"
    | Cfg uu____1457 -> "Cfg"
    | Debug (t,uu____1459) ->
        let uu____1460 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1460
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1468 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1468 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1484 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1484 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1497 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1497 then f () else ()
let is_empty: 'Auu____1501 . 'Auu____1501 Prims.list -> Prims.bool =
  fun uu___77_1507  ->
    match uu___77_1507 with | [] -> true | uu____1510 -> false
let lookup_bvar:
  'Auu____1517 'Auu____1518 .
    ('Auu____1518,'Auu____1517) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1517
  =
  fun env  ->
    fun x  ->
      try
        let uu____1542 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1542
      with
      | uu____1555 ->
          let uu____1556 =
            let uu____1557 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1557 in
          failwith uu____1556
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let norm_universe:
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1594 =
            FStar_List.fold_left
              (fun uu____1620  ->
                 fun u1  ->
                   match uu____1620 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1645 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1645 with
                        | (k_u,n1) ->
                            let uu____1660 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1660
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1594 with
          | (uu____1678,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1704 =
                   let uu____1705 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1705 in
                 match uu____1704 with
                 | Univ u3 ->
                     ((let uu____1724 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug cfg.tcenv)
                           (FStar_Options.Other "univ_norm") in
                       if uu____1724
                       then
                         let uu____1725 =
                           FStar_Syntax_Print.univ_to_string u3 in
                         FStar_Util.print1 "Univ (in norm_universe): %s\n"
                           uu____1725
                       else ());
                      aux u3)
                 | Dummy  -> [u2]
                 | uu____1727 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1736 ->
                   let uu____1737 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1737
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1743 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1752 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1761 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1768 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1768 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1785 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1785 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1793 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1801 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1801 with
                                  | (uu____1806,m) -> n1 <= m)) in
                        if uu____1793 then rest1 else us1
                    | uu____1811 -> us1)
               | uu____1816 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1820 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1820 in
        let uu____1823 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1823
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1825 = aux u in
           match uu____1825 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____1929  ->
             let uu____1930 = FStar_Syntax_Print.tag_of_term t in
             let uu____1931 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1930
               uu____1931);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1938 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1940 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1965 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1966 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1967 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1968 ->
                  let uu____1985 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1985
                  then
                    let uu____1986 =
                      let uu____1987 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1988 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1987 uu____1988 in
                    failwith uu____1986
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1991 =
                    let uu____1992 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1992 in
                  mk uu____1991 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1999 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1999
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2001 = lookup_bvar env x in
                  (match uu____2001 with
                   | Univ uu____2004 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____2007,uu____2008) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2120 = closures_as_binders_delayed cfg env bs in
                  (match uu____2120 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2148 =
                         let uu____2149 =
                           let uu____2166 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2166) in
                         FStar_Syntax_Syntax.Tm_abs uu____2149 in
                       mk uu____2148 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2197 = closures_as_binders_delayed cfg env bs in
                  (match uu____2197 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2239 =
                    let uu____2250 =
                      let uu____2257 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2257] in
                    closures_as_binders_delayed cfg env uu____2250 in
                  (match uu____2239 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2275 =
                         let uu____2276 =
                           let uu____2283 =
                             let uu____2284 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2284
                               FStar_Pervasives_Native.fst in
                           (uu____2283, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2276 in
                       mk uu____2275 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2375 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2375
                    | FStar_Util.Inr c ->
                        let uu____2389 = close_comp cfg env c in
                        FStar_Util.Inr uu____2389 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2405 =
                    let uu____2406 =
                      let uu____2433 = closure_as_term_delayed cfg env t11 in
                      (uu____2433, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2406 in
                  mk uu____2405 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2484 =
                    let uu____2485 =
                      let uu____2492 = closure_as_term_delayed cfg env t' in
                      let uu____2495 =
                        let uu____2496 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2496 in
                      (uu____2492, uu____2495) in
                    FStar_Syntax_Syntax.Tm_meta uu____2485 in
                  mk uu____2484 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2556 =
                    let uu____2557 =
                      let uu____2564 = closure_as_term_delayed cfg env t' in
                      let uu____2567 =
                        let uu____2568 =
                          let uu____2575 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2575) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2568 in
                      (uu____2564, uu____2567) in
                    FStar_Syntax_Syntax.Tm_meta uu____2557 in
                  mk uu____2556 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2594 =
                    let uu____2595 =
                      let uu____2602 = closure_as_term_delayed cfg env t' in
                      let uu____2605 =
                        let uu____2606 =
                          let uu____2615 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2615) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2606 in
                      (uu____2602, uu____2605) in
                    FStar_Syntax_Syntax.Tm_meta uu____2595 in
                  mk uu____2594 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2628 =
                    let uu____2629 =
                      let uu____2636 = closure_as_term_delayed cfg env t' in
                      (uu____2636, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2629 in
                  mk uu____2628 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2676  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2695 =
                    let uu____2706 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2706
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2725 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___98_2737 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___98_2737.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___98_2737.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2725)) in
                  (match uu____2695 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___99_2753 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___99_2753.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___99_2753.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___99_2753.FStar_Syntax_Syntax.lbattrs)
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2764,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2823  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2848 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2848
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2868  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2890 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2890
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___100_2902 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___100_2902.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___100_2902.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___101_2903 = lb in
                    let uu____2904 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___101_2903.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___101_2903.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2904;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___101_2903.FStar_Syntax_Syntax.lbattrs)
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2934  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3023 =
                    match uu____3023 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3078 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3099 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3159  ->
                                        fun uu____3160  ->
                                          match (uu____3159, uu____3160) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3251 =
                                                norm_pat env3 p1 in
                                              (match uu____3251 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3099 with
                               | (pats1,env3) ->
                                   ((let uu___102_3333 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___102_3333.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___103_3352 = x in
                                let uu____3353 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___103_3352.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___103_3352.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3353
                                } in
                              ((let uu___104_3367 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___104_3367.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___105_3378 = x in
                                let uu____3379 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___105_3378.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___105_3378.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3379
                                } in
                              ((let uu___106_3393 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___106_3393.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___107_3409 = x in
                                let uu____3410 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___107_3409.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___107_3409.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3410
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___108_3417 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___108_3417.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3420 = norm_pat env1 pat in
                        (match uu____3420 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3449 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3449 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3455 =
                    let uu____3456 =
                      let uu____3479 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3479) in
                    FStar_Syntax_Syntax.Tm_match uu____3456 in
                  mk uu____3455 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3565 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____3591 ->
            FStar_List.map
              (fun uu____3608  ->
                 match uu____3608 with
                 | (x,imp) ->
                     let uu____3627 = closure_as_term_delayed cfg env x in
                     (uu____3627, imp)) args
and closures_as_binders_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3641 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3690  ->
                  fun uu____3691  ->
                    match (uu____3690, uu____3691) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___109_3761 = b in
                          let uu____3762 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___109_3761.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___109_3761.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3762
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3641 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____3855 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3868 = closure_as_term_delayed cfg env t in
                 let uu____3869 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3868 uu____3869
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3882 = closure_as_term_delayed cfg env t in
                 let uu____3883 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3882 uu____3883
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___78_3909  ->
                           match uu___78_3909 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3913 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3913
                           | f -> f)) in
                 let uu____3917 =
                   let uu___110_3918 = c1 in
                   let uu____3919 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3919;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___110_3918.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3917)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___79_3929  ->
            match uu___79_3929 with
            | FStar_Syntax_Syntax.DECREASES uu____3930 -> false
            | uu____3933 -> true))
and close_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___80_3951  ->
                      match uu___80_3951 with
                      | FStar_Syntax_Syntax.DECREASES uu____3952 -> false
                      | uu____3955 -> true)) in
            let rc1 =
              let uu___111_3957 = rc in
              let uu____3958 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___111_3957.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3958;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3965 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe in
  let arg_as_list a u a =
    let uu____4050 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4050 in
  let arg_as_bounded_int uu____4078 =
    match uu____4078 with
    | (a,uu____4090) ->
        let uu____4097 =
          let uu____4098 = FStar_Syntax_Subst.compress a in
          uu____4098.FStar_Syntax_Syntax.n in
        (match uu____4097 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4108;
                FStar_Syntax_Syntax.vars = uu____4109;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4111;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4112;_},uu____4113)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4152 =
               let uu____4157 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4157) in
             FStar_Pervasives_Native.Some uu____4152
         | uu____4162 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4202 = f a in FStar_Pervasives_Native.Some uu____4202
    | uu____4203 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4251 = f a0 a1 in FStar_Pervasives_Native.Some uu____4251
    | uu____4252 -> FStar_Pervasives_Native.None in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4294 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____4294)) a416 a417 a418 a419 a420 in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4343 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____4343)) a423 a424 a425 a426 a427 in
  let as_primitive_step uu____4367 =
    match uu____4367 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4415 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4415)) a429 a430) in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4443 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4443)) a432
               a433 a434) in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4464 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4464)) a436
             a437) in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4492 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4492)) a439
               a440 a441) in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4520 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4520))
               a443 a444 a445) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4628 =
          let uu____4637 = as_a a in
          let uu____4640 = as_b b in (uu____4637, uu____4640) in
        (match uu____4628 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4655 =
               let uu____4656 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4656 in
             FStar_Pervasives_Native.Some uu____4655
         | uu____4657 -> FStar_Pervasives_Native.None)
    | uu____4666 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4680 =
        let uu____4681 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4681 in
      mk uu____4680 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4691 =
      let uu____4694 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4694 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4691 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4726 =
      let uu____4727 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4727 in
    FStar_Syntax_Embeddings.embed_int rng uu____4726 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4745 = arg_as_string a1 in
        (match uu____4745 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4751 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4751 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4764 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4764
              | uu____4765 -> FStar_Pervasives_Native.None)
         | uu____4770 -> FStar_Pervasives_Native.None)
    | uu____4773 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4783 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4783 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4807 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4818 =
          let uu____4839 = arg_as_string fn in
          let uu____4842 = arg_as_int from_line in
          let uu____4845 = arg_as_int from_col in
          let uu____4848 = arg_as_int to_line in
          let uu____4851 = arg_as_int to_col in
          (uu____4839, uu____4842, uu____4845, uu____4848, uu____4851) in
        (match uu____4818 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4882 =
                 let uu____4883 = FStar_BigInt.to_int_fs from_l in
                 let uu____4884 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4883 uu____4884 in
               let uu____4885 =
                 let uu____4886 = FStar_BigInt.to_int_fs to_l in
                 let uu____4887 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4886 uu____4887 in
               FStar_Range.mk_range fn1 uu____4882 uu____4885 in
             let uu____4888 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4888
         | uu____4893 -> FStar_Pervasives_Native.None)
    | uu____4914 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4941)::(a1,uu____4943)::(a2,uu____4945)::[] ->
        let uu____4982 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4982 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4995 -> FStar_Pervasives_Native.None)
    | uu____4996 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5023)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5032 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5056 =
      let uu____5071 =
        let uu____5086 =
          let uu____5101 =
            let uu____5116 =
              let uu____5131 =
                let uu____5146 =
                  let uu____5161 =
                    let uu____5176 =
                      let uu____5191 =
                        let uu____5206 =
                          let uu____5221 =
                            let uu____5236 =
                              let uu____5251 =
                                let uu____5266 =
                                  let uu____5281 =
                                    let uu____5296 =
                                      let uu____5311 =
                                        let uu____5326 =
                                          let uu____5341 =
                                            let uu____5356 =
                                              let uu____5371 =
                                                let uu____5384 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5384,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448))) in
                                              let uu____5391 =
                                                let uu____5406 =
                                                  let uu____5419 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5419,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451))) in
                                                let uu____5426 =
                                                  let uu____5441 =
                                                    let uu____5456 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5456,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5465 =
                                                    let uu____5482 =
                                                      let uu____5497 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5497,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5506 =
                                                      let uu____5523 =
                                                        let uu____5542 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5542,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5523] in
                                                    uu____5482 :: uu____5506 in
                                                  uu____5441 :: uu____5465 in
                                                uu____5406 :: uu____5426 in
                                              uu____5371 :: uu____5391 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5356 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5341 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____5326 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____5311 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____5296 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____5759 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5759 y)) a466
                                                a467 a468)))
                                    :: uu____5281 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5266 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5251 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5236 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5221 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5206 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5191 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____5926 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5926)) a470 a471 a472)))
                      :: uu____5176 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5952 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5952)) a474 a475 a476)))
                    :: uu____5161 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5978 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5978)) a478 a479 a480)))
                  :: uu____5146 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____6004 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____6004)) a482 a483 a484)))
                :: uu____5131 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5116 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5101 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5086 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5071 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5056 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6157 =
        let uu____6158 =
          let uu____6159 = FStar_Syntax_Syntax.as_arg c in [uu____6159] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6158 in
      uu____6157 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6209 =
                let uu____6222 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6222, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6238  ->
                                    fun uu____6239  ->
                                      match (uu____6238, uu____6239) with
                                      | ((int_to_t1,x),(uu____6258,y)) ->
                                          let uu____6268 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6268)) a486 a487 a488))) in
              let uu____6269 =
                let uu____6284 =
                  let uu____6297 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6297, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6313  ->
                                      fun uu____6314  ->
                                        match (uu____6313, uu____6314) with
                                        | ((int_to_t1,x),(uu____6333,y)) ->
                                            let uu____6343 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6343)) a490 a491 a492))) in
                let uu____6344 =
                  let uu____6359 =
                    let uu____6372 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6372, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6388  ->
                                        fun uu____6389  ->
                                          match (uu____6388, uu____6389) with
                                          | ((int_to_t1,x),(uu____6408,y)) ->
                                              let uu____6418 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____6418)) a494 a495 a496))) in
                  let uu____6419 =
                    let uu____6434 =
                      let uu____6447 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____6447, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6459  ->
                                        match uu____6459 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499))) in
                    [uu____6434] in
                  uu____6359 :: uu____6419 in
                uu____6284 :: uu____6344 in
              uu____6209 :: uu____6269)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6573 =
                let uu____6586 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6586, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6602  ->
                                    fun uu____6603  ->
                                      match (uu____6602, uu____6603) with
                                      | ((int_to_t1,x),(uu____6622,y)) ->
                                          let uu____6632 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6632)) a501 a502 a503))) in
              let uu____6633 =
                let uu____6648 =
                  let uu____6661 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6661, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6677  ->
                                      fun uu____6678  ->
                                        match (uu____6677, uu____6678) with
                                        | ((int_to_t1,x),(uu____6697,y)) ->
                                            let uu____6707 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6707)) a505 a506 a507))) in
                [uu____6648] in
              uu____6573 :: uu____6633)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6797)::(a1,uu____6799)::(a2,uu____6801)::[] ->
        let uu____6838 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6838 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6844 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6844.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6844.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___113_6848 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___113_6848.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___113_6848.FStar_Syntax_Syntax.vars)
                })
         | uu____6849 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6851)::uu____6852::(a1,uu____6854)::(a2,uu____6856)::[] ->
        let uu____6905 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6905 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6911 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6911.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6911.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___113_6915 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___113_6915.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___113_6915.FStar_Syntax_Syntax.vars)
                })
         | uu____6916 -> FStar_Pervasives_Native.None)
    | uu____6917 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  [propositional_equality; hetero_propositional_equality]
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____6936 =
        let uu____6937 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6937 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6936
    with | uu____6943 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6947 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6947) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7007  ->
           fun subst1  ->
             match uu____7007 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____7048,uu____7049)) ->
                      let uu____7108 = b in
                      (match uu____7108 with
                       | (bv,uu____7116) ->
                           let uu____7117 =
                             let uu____7118 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7118 in
                           if uu____7117
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7123 = unembed_binder term1 in
                              match uu____7123 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7130 =
                                      let uu___116_7131 = bv in
                                      let uu____7132 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___116_7131.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___116_7131.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7132
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7130 in
                                  let b_for_x =
                                    let uu____7136 =
                                      let uu____7143 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7143) in
                                    FStar_Syntax_Syntax.NT uu____7136 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___81_7152  ->
                                         match uu___81_7152 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7153,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7155;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7156;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7161 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7162 -> subst1)) env []
let reduce_primops:
  'Auu____7179 'Auu____7180 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7180) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7179 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7221 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7221
          then tm
          else
            (let uu____7223 = FStar_Syntax_Util.head_and_args tm in
             match uu____7223 with
             | (head1,args) ->
                 let uu____7260 =
                   let uu____7261 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7261.FStar_Syntax_Syntax.n in
                 (match uu____7260 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7265 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7265 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7282  ->
                                   let uu____7283 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7284 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7291 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7283 uu____7284 uu____7291);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7296  ->
                                   let uu____7297 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7297);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7300  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7302 =
                                 prim_step.interpretation psc args in
                               match uu____7302 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7308  ->
                                         let uu____7309 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7309);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7315  ->
                                         let uu____7316 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7317 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7316 uu____7317);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7318 ->
                           (log_primops cfg
                              (fun uu____7322  ->
                                 let uu____7323 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7323);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7327  ->
                            let uu____7328 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7328);
                       (match args with
                        | (a1,uu____7330)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7347 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7359  ->
                            let uu____7360 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7360);
                       (match args with
                        | (t,uu____7362)::(r,uu____7364)::[] ->
                            let uu____7391 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7391 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___117_7395 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___117_7395.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___117_7395.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7398 -> tm))
                  | uu____7407 -> tm))
let reduce_equality:
  'Auu____7412 'Auu____7413 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7413) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7412 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___118_7451 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___118_7451.tcenv);
           delta_level = (uu___118_7451.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___118_7451.strong);
           memoize_lazy = (uu___118_7451.memoize_lazy);
           normalize_pure_lets = (uu___118_7451.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____7458 'Auu____7459 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7459) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7458 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7501 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7501
          then tm1
          else
            (let w t =
               let uu___119_7513 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___119_7513.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___119_7513.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7529;
                      FStar_Syntax_Syntax.vars = uu____7530;_},uu____7531)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7538;
                      FStar_Syntax_Syntax.vars = uu____7539;_},uu____7540)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7546 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7551 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7551
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7572 =
                 match uu____7572 with
                 | (t1,q) ->
                     let uu____7585 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7585 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7613 -> (t1, q)) in
               let uu____7622 = FStar_Syntax_Util.head_and_args t in
               match uu____7622 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7719;
                         FStar_Syntax_Syntax.vars = uu____7720;_},uu____7721);
                    FStar_Syntax_Syntax.pos = uu____7722;
                    FStar_Syntax_Syntax.vars = uu____7723;_},args)
                 ->
                 let uu____7749 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7749
                 then
                   let uu____7750 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7750 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7805)::
                        (uu____7806,(arg,uu____7808))::[] ->
                        maybe_auto_squash arg
                    | (uu____7873,(arg,uu____7875))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7876)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7941)::uu____7942::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8005::(FStar_Pervasives_Native.Some (false
                                   ),uu____8006)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8069 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8085 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8085
                    then
                      let uu____8086 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8086 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8141)::uu____8142::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8205::(FStar_Pervasives_Native.Some (true
                                     ),uu____8206)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8269)::
                          (uu____8270,(arg,uu____8272))::[] ->
                          maybe_auto_squash arg
                      | (uu____8337,(arg,uu____8339))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8340)::[]
                          -> maybe_auto_squash arg
                      | uu____8405 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8421 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8421
                       then
                         let uu____8422 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8422 with
                         | uu____8477::(FStar_Pervasives_Native.Some (true
                                        ),uu____8478)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8541)::uu____8542::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8605)::
                             (uu____8606,(arg,uu____8608))::[] ->
                             maybe_auto_squash arg
                         | (uu____8673,(p,uu____8675))::(uu____8676,(q,uu____8678))::[]
                             ->
                             let uu____8743 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8743
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8745 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8761 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8761
                          then
                            let uu____8762 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8762 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8817)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8856)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8895 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8911 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8911
                             then
                               match args with
                               | (t,uu____8913)::[] ->
                                   let uu____8930 =
                                     let uu____8931 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8931.FStar_Syntax_Syntax.n in
                                   (match uu____8930 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8934::[],body,uu____8936) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8963 -> tm1)
                                    | uu____8966 -> tm1)
                               | (uu____8967,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8968))::
                                   (t,uu____8970)::[] ->
                                   let uu____9009 =
                                     let uu____9010 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9010.FStar_Syntax_Syntax.n in
                                   (match uu____9009 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9013::[],body,uu____9015) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9042 -> tm1)
                                    | uu____9045 -> tm1)
                               | uu____9046 -> tm1
                             else
                               (let uu____9056 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9056
                                then
                                  match args with
                                  | (t,uu____9058)::[] ->
                                      let uu____9075 =
                                        let uu____9076 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9076.FStar_Syntax_Syntax.n in
                                      (match uu____9075 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9079::[],body,uu____9081)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9108 -> tm1)
                                       | uu____9111 -> tm1)
                                  | (uu____9112,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9113))::(t,uu____9115)::[] ->
                                      let uu____9154 =
                                        let uu____9155 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9155.FStar_Syntax_Syntax.n in
                                      (match uu____9154 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9158::[],body,uu____9160)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9187 -> tm1)
                                       | uu____9190 -> tm1)
                                  | uu____9191 -> tm1
                                else
                                  (let uu____9201 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9201
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9202;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9203;_},uu____9204)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9221;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9222;_},uu____9223)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9240 -> tm1
                                   else
                                     (let uu____9250 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9250 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9270 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9280;
                    FStar_Syntax_Syntax.vars = uu____9281;_},args)
                 ->
                 let uu____9303 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9303
                 then
                   let uu____9304 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9304 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9359)::
                        (uu____9360,(arg,uu____9362))::[] ->
                        maybe_auto_squash arg
                    | (uu____9427,(arg,uu____9429))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9430)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9495)::uu____9496::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9559::(FStar_Pervasives_Native.Some (false
                                   ),uu____9560)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9623 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9639 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9639
                    then
                      let uu____9640 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9640 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9695)::uu____9696::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9759::(FStar_Pervasives_Native.Some (true
                                     ),uu____9760)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9823)::
                          (uu____9824,(arg,uu____9826))::[] ->
                          maybe_auto_squash arg
                      | (uu____9891,(arg,uu____9893))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9894)::[]
                          -> maybe_auto_squash arg
                      | uu____9959 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9975 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9975
                       then
                         let uu____9976 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9976 with
                         | uu____10031::(FStar_Pervasives_Native.Some (true
                                         ),uu____10032)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10095)::uu____10096::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10159)::
                             (uu____10160,(arg,uu____10162))::[] ->
                             maybe_auto_squash arg
                         | (uu____10227,(p,uu____10229))::(uu____10230,
                                                           (q,uu____10232))::[]
                             ->
                             let uu____10297 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10297
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10299 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10315 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10315
                          then
                            let uu____10316 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10316 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10371)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10410)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10449 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10465 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10465
                             then
                               match args with
                               | (t,uu____10467)::[] ->
                                   let uu____10484 =
                                     let uu____10485 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10485.FStar_Syntax_Syntax.n in
                                   (match uu____10484 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10488::[],body,uu____10490) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10517 -> tm1)
                                    | uu____10520 -> tm1)
                               | (uu____10521,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10522))::
                                   (t,uu____10524)::[] ->
                                   let uu____10563 =
                                     let uu____10564 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10564.FStar_Syntax_Syntax.n in
                                   (match uu____10563 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10567::[],body,uu____10569) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10596 -> tm1)
                                    | uu____10599 -> tm1)
                               | uu____10600 -> tm1
                             else
                               (let uu____10610 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10610
                                then
                                  match args with
                                  | (t,uu____10612)::[] ->
                                      let uu____10629 =
                                        let uu____10630 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10630.FStar_Syntax_Syntax.n in
                                      (match uu____10629 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10633::[],body,uu____10635)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10662 -> tm1)
                                       | uu____10665 -> tm1)
                                  | (uu____10666,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10667))::(t,uu____10669)::[] ->
                                      let uu____10708 =
                                        let uu____10709 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10709.FStar_Syntax_Syntax.n in
                                      (match uu____10708 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10712::[],body,uu____10714)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10741 -> tm1)
                                       | uu____10744 -> tm1)
                                  | uu____10745 -> tm1
                                else
                                  (let uu____10755 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10755
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10756;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10757;_},uu____10758)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10775;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10776;_},uu____10777)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10794 -> tm1
                                   else
                                     (let uu____10804 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10804 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10824 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____10839 -> tm1)
let maybe_simplify:
  'Auu____10846 'Auu____10847 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10847) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10846 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10890 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10890
           then
             let uu____10891 = FStar_Syntax_Print.term_to_string tm in
             let uu____10892 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10891 uu____10892
           else ());
          tm'
let is_norm_request:
  'Auu____10898 .
    FStar_Syntax_Syntax.term -> 'Auu____10898 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10911 =
        let uu____10918 =
          let uu____10919 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10919.FStar_Syntax_Syntax.n in
        (uu____10918, args) in
      match uu____10911 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10925::uu____10926::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10930::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10935::uu____10936::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10939 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___82_10950  ->
    match uu___82_10950 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10956 =
          let uu____10959 =
            let uu____10960 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10960 in
          [uu____10959] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10956
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10976 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10976) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11014 =
          let uu____11017 =
            let uu____11022 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____11022 s in
          FStar_All.pipe_right uu____11017 FStar_Util.must in
        FStar_All.pipe_right uu____11014 tr_norm_steps in
      match args with
      | uu____11047::(tm,uu____11049)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11072)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11087)::uu____11088::(tm,uu____11090)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11130 =
              let uu____11133 = full_norm steps in parse_steps uu____11133 in
            Beta :: uu____11130 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11142 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___83_11159  ->
    match uu___83_11159 with
    | (App
        (uu____11162,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11163;
                       FStar_Syntax_Syntax.vars = uu____11164;_},uu____11165,uu____11166))::uu____11167
        -> true
    | uu____11174 -> false
let firstn:
  'Auu____11180 .
    Prims.int ->
      'Auu____11180 Prims.list ->
        ('Auu____11180 Prims.list,'Auu____11180 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____11216,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11217;
                         FStar_Syntax_Syntax.vars = uu____11218;_},uu____11219,uu____11220))::uu____11221
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11228 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            (let uu____11370 =
               FStar_TypeChecker_Env.debug cfg.tcenv
                 (FStar_Options.Other "NormDelayed") in
             if uu____11370
             then
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____11371 ->
                   let uu____11396 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11396
               | uu____11397 -> ()
             else ());
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11406  ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               let uu____11408 = FStar_Syntax_Print.tag_of_term t2 in
               let uu____11409 = FStar_Syntax_Print.term_to_string t2 in
               let uu____11410 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11417 =
                 let uu____11418 =
                   let uu____11421 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11421 in
                 stack_to_string uu____11418 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11408 uu____11409 uu____11410 uu____11417);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11444 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11445 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11446;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11447;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11450;
                 FStar_Syntax_Syntax.fv_delta = uu____11451;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11452;
                 FStar_Syntax_Syntax.fv_delta = uu____11453;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11454);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11462 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11462 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11468  ->
                     let uu____11469 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11470 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11469 uu____11470);
                if b
                then
                  (let uu____11471 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11471 t1 fv)
                else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___120_11510 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___120_11510.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___120_11510.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11543 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11543) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___121_11551 = cfg in
                 let uu____11552 =
                   FStar_List.filter
                     (fun uu___84_11555  ->
                        match uu___84_11555 with
                        | UnfoldOnly uu____11556 -> false
                        | NoDeltaSteps  -> false
                        | uu____11559 -> true) cfg.steps in
                 {
                   steps = uu____11552;
                   tcenv = (uu___121_11551.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___121_11551.primitive_steps);
                   strong = (uu___121_11551.strong);
                   memoize_lazy = (uu___121_11551.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____11560 = get_norm_request (norm cfg' env []) args in
               (match uu____11560 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11576 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___85_11581  ->
                                match uu___85_11581 with
                                | UnfoldUntil uu____11582 -> true
                                | UnfoldOnly uu____11583 -> true
                                | uu____11586 -> false)) in
                      if uu____11576
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___122_11591 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___122_11591.tcenv);
                        delta_level;
                        primitive_steps = (uu___122_11591.primitive_steps);
                        strong = (uu___122_11591.strong);
                        memoize_lazy = (uu___122_11591.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11598 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11598
                      then
                        let uu____11601 =
                          let uu____11602 =
                            let uu____11607 = FStar_Util.now () in
                            (t1, uu____11607) in
                          Debug uu____11602 in
                        uu____11601 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11611 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11611
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11618 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11618
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11621 =
                      let uu____11628 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11628, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11621 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___86_11641  ->
                         match uu___86_11641 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11644 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     ((((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.and_lid)
                                ||
                                (FStar_Syntax_Syntax.fv_eq_lid f
                                   FStar_Parser_Const.or_lid))
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Parser_Const.imp_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.forall_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.squash_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Parser_Const.exists_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Parser_Const.eq2_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Parser_Const.eq3_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid)) in
                 if uu____11644
                 then false
                 else
                   (let uu____11646 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___87_11653  ->
                              match uu___87_11653 with
                              | UnfoldOnly uu____11654 -> true
                              | UnfoldAttr uu____11657 -> true
                              | uu____11658 -> false)) in
                    match uu____11646 with
                    | FStar_Pervasives_Native.Some uu____11659 ->
                        let attr_eq a a' =
                          let uu____11667 = FStar_Syntax_Util.eq_tm a a' in
                          match uu____11667 with
                          | FStar_Syntax_Util.Equal  -> true
                          | uu____11668 -> false in
                        should_delta &&
                          (FStar_List.fold_left
                             (fun acc  ->
                                fun x  ->
                                  match x with
                                  | UnfoldOnly lids ->
                                      acc ||
                                        (FStar_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid f)
                                           lids)
                                  | UnfoldAttr attr ->
                                      let uu____11678 =
                                        FStar_TypeChecker_Env.lookup_attrs_of_lid
                                          cfg.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      (match uu____11678 with
                                       | FStar_Pervasives_Native.Some attrs
                                           ->
                                           acc ||
                                             (FStar_Util.for_some
                                                (attr_eq attr) attrs)
                                       | uu____11688 -> acc)
                                  | uu____11693 -> acc) false cfg.steps)
                    | uu____11694 -> should_delta) in
               (log cfg
                  (fun uu____11702  ->
                     let uu____11703 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11704 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11705 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11703 uu____11704 uu____11705);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11708 = lookup_bvar env x in
               (match uu____11708 with
                | Univ uu____11711 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11760 = FStar_ST.op_Bang r in
                      (match uu____11760 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11878  ->
                                 let uu____11879 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11880 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11879
                                   uu____11880);
                            (let uu____11881 =
                               let uu____11882 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11882.FStar_Syntax_Syntax.n in
                             match uu____11881 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11885 ->
                                 norm cfg env2 stack t'
                             | uu____11902 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11972)::uu____11973 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11982)::uu____11983 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11993,uu____11994))::stack_rest ->
                    (match c with
                     | Univ uu____11998 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12007 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12028  ->
                                    let uu____12029 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12029);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12069  ->
                                    let uu____12070 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12070);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____12148  ->
                          let uu____12149 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12149);
                     norm cfg env stack1 t1)
                | (Debug uu____12150)::uu____12151 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12158 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12158
                    else
                      (let uu____12160 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12160 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12202  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12230 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12230
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12240 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12240)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___123_12245 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___123_12245.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___123_12245.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12246 -> lopt in
                           (log cfg
                              (fun uu____12252  ->
                                 let uu____12253 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12253);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___124_12262 = cfg in
                               {
                                 steps = (uu___124_12262.steps);
                                 tcenv = (uu___124_12262.tcenv);
                                 delta_level = (uu___124_12262.delta_level);
                                 primitive_steps =
                                   (uu___124_12262.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___124_12262.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___124_12262.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12273)::uu____12274 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12281 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12281
                    else
                      (let uu____12283 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12283 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12325  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12353 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12353
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12363 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12363)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___123_12368 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___123_12368.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___123_12368.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12369 -> lopt in
                           (log cfg
                              (fun uu____12375  ->
                                 let uu____12376 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12376);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___124_12385 = cfg in
                               {
                                 steps = (uu___124_12385.steps);
                                 tcenv = (uu___124_12385.tcenv);
                                 delta_level = (uu___124_12385.delta_level);
                                 primitive_steps =
                                   (uu___124_12385.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___124_12385.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___124_12385.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12396)::uu____12397 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12408 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12408
                    else
                      (let uu____12410 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12410 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12452  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12480 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12480
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12490 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12490)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___123_12495 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___123_12495.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___123_12495.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12496 -> lopt in
                           (log cfg
                              (fun uu____12502  ->
                                 let uu____12503 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12503);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___124_12512 = cfg in
                               {
                                 steps = (uu___124_12512.steps);
                                 tcenv = (uu___124_12512.tcenv);
                                 delta_level = (uu___124_12512.delta_level);
                                 primitive_steps =
                                   (uu___124_12512.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___124_12512.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___124_12512.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12523)::uu____12524 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12535 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12535
                    else
                      (let uu____12537 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12537 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12579  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12607 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12607
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12617 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12617)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___123_12622 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___123_12622.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___123_12622.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12623 -> lopt in
                           (log cfg
                              (fun uu____12629  ->
                                 let uu____12630 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12630);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___124_12639 = cfg in
                               {
                                 steps = (uu___124_12639.steps);
                                 tcenv = (uu___124_12639.tcenv);
                                 delta_level = (uu___124_12639.delta_level);
                                 primitive_steps =
                                   (uu___124_12639.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___124_12639.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___124_12639.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12650)::uu____12651 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12666 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12666
                    else
                      (let uu____12668 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12668 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12710  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12738 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12738
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12748 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12748)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___123_12753 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___123_12753.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___123_12753.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12754 -> lopt in
                           (log cfg
                              (fun uu____12760  ->
                                 let uu____12761 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12761);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___124_12770 = cfg in
                               {
                                 steps = (uu___124_12770.steps);
                                 tcenv = (uu___124_12770.tcenv);
                                 delta_level = (uu___124_12770.delta_level);
                                 primitive_steps =
                                   (uu___124_12770.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___124_12770.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___124_12770.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12781 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12781
                    else
                      (let uu____12783 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12783 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12825  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12853 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12853
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12863 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12863)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___123_12868 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___123_12868.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___123_12868.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12869 -> lopt in
                           (log cfg
                              (fun uu____12875  ->
                                 let uu____12876 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12876);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___124_12885 = cfg in
                               {
                                 steps = (uu___124_12885.steps);
                                 tcenv = (uu___124_12885.tcenv);
                                 delta_level = (uu___124_12885.delta_level);
                                 primitive_steps =
                                   (uu___124_12885.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___124_12885.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___124_12885.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____12934  ->
                         fun stack1  ->
                           match uu____12934 with
                           | (a,aq) ->
                               let uu____12946 =
                                 let uu____12947 =
                                   let uu____12954 =
                                     let uu____12955 =
                                       let uu____12986 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12986, false) in
                                     Clos uu____12955 in
                                   (uu____12954, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12947 in
                               uu____12946 :: stack1) args) in
               (log cfg
                  (fun uu____13070  ->
                     let uu____13071 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13071);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___125_13107 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___125_13107.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___125_13107.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13108 ->
                      let uu____13113 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13113)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13116 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13116 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13147 =
                          let uu____13148 =
                            let uu____13155 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___126_13157 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_13157.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_13157.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13155) in
                          FStar_Syntax_Syntax.Tm_refine uu____13148 in
                        mk uu____13147 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13176 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13176
               else
                 (let uu____13178 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13178 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13186 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13210  -> dummy :: env1) env) in
                        norm_comp cfg uu____13186 c1 in
                      let t2 =
                        let uu____13232 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13232 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               FStar_List.contains Unascribe cfg.steps ->
               norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13343)::uu____13344 ->
                    (log cfg
                       (fun uu____13355  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13356)::uu____13357 ->
                    (log cfg
                       (fun uu____13368  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13369,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13370;
                                   FStar_Syntax_Syntax.vars = uu____13371;_},uu____13372,uu____13373))::uu____13374
                    ->
                    (log cfg
                       (fun uu____13383  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13384)::uu____13385 ->
                    (log cfg
                       (fun uu____13396  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13397 ->
                    (log cfg
                       (fun uu____13400  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13404  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13421 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13421
                         | FStar_Util.Inr c ->
                             let uu____13429 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13429 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13442 =
                               let uu____13443 =
                                 let uu____13470 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13470, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13443 in
                             mk uu____13442 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13489 ->
                           let uu____13490 =
                             let uu____13491 =
                               let uu____13492 =
                                 let uu____13519 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13519, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13492 in
                             mk uu____13491 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13490))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (FStar_List.contains CompressUvars cfg.steps)
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____13629 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13629 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___127_13649 = cfg in
                               let uu____13650 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___127_13649.steps);
                                 tcenv = uu____13650;
                                 delta_level = (uu___127_13649.delta_level);
                                 primitive_steps =
                                   (uu___127_13649.primitive_steps);
                                 strong = (uu___127_13649.strong);
                                 memoize_lazy = (uu___127_13649.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___127_13649.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____13655 =
                                 let uu____13656 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13656 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13655 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___128_13659 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___128_13659.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___128_13659.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___128_13659.FStar_Syntax_Syntax.lbattrs)
                             })) in
               let uu____13660 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13660
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13671,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13672;
                               FStar_Syntax_Syntax.lbunivs = uu____13673;
                               FStar_Syntax_Syntax.lbtyp = uu____13674;
                               FStar_Syntax_Syntax.lbeff = uu____13675;
                               FStar_Syntax_Syntax.lbdef = uu____13676;
                               FStar_Syntax_Syntax.lbattrs = uu____13677;_}::uu____13678),uu____13679)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13719 =
                 (let uu____13722 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13722) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       (cfg.normalize_pure_lets ||
                          (FStar_Util.for_some
                             (FStar_Syntax_Util.is_fvar
                                FStar_Parser_Const.inline_let_attr)
                             lb.FStar_Syntax_Syntax.lbattrs)))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13724 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13724))) in
               if uu____13719
               then
                 let binder =
                   let uu____13726 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13726 in
                 let env1 =
                   let uu____13736 =
                     let uu____13743 =
                       let uu____13744 =
                         let uu____13775 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13775,
                           false) in
                       Clos uu____13744 in
                     ((FStar_Pervasives_Native.Some binder), uu____13743) in
                   uu____13736 :: env in
                 (log cfg
                    (fun uu____13868  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if FStar_List.contains Weak cfg.steps
                 then
                   (log cfg
                      (fun uu____13872  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13873 = closure_as_term cfg env t1 in
                     rebuild cfg env stack uu____13873))
                 else
                   (let uu____13875 =
                      let uu____13880 =
                        let uu____13881 =
                          let uu____13882 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____13882
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____13881] in
                      FStar_Syntax_Subst.open_term uu____13880 body in
                    match uu____13875 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13891  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                          let lbname =
                            let x =
                              let uu____13899 = FStar_List.hd bs in
                              FStar_Pervasives_Native.fst uu____13899 in
                            FStar_Util.Inl
                              (let uu___129_13909 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___129_13909.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___129_13909.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }) in
                          log cfg
                            (fun uu____13912  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___130_13914 = lb in
                             let uu____13915 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___130_13914.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___130_13914.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13915;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___130_13914.FStar_Syntax_Syntax.lbattrs)
                             } in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13950  -> dummy :: env1) env) in
                           let stack1 = (Cfg cfg) :: stack in
                           let cfg1 =
                             let uu___131_13973 = cfg in
                             {
                               steps = (uu___131_13973.steps);
                               tcenv = (uu___131_13973.tcenv);
                               delta_level = (uu___131_13973.delta_level);
                               primitive_steps =
                                 (uu___131_13973.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___131_13973.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___131_13973.normalize_pure_lets)
                             } in
                           log cfg1
                             (fun uu____13976  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13993 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13993 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14029 =
                               let uu___132_14030 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___132_14030.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___132_14030.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14029 in
                           let uu____14031 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14031 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14057 =
                                   FStar_List.map (fun uu____14073  -> dummy)
                                     lbs1 in
                                 let uu____14074 =
                                   let uu____14083 =
                                     FStar_List.map
                                       (fun uu____14103  -> dummy) xs1 in
                                   FStar_List.append uu____14083 env in
                                 FStar_List.append uu____14057 uu____14074 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14127 =
                                       let uu___133_14128 = rc in
                                       let uu____14129 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___133_14128.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14129;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___133_14128.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14127
                                 | uu____14136 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___134_14140 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_14140.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_14140.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_14140.FStar_Syntax_Syntax.lbattrs)
                               }) lbs1 in
                    let env' =
                      let uu____14150 =
                        FStar_List.map (fun uu____14166  -> dummy) lbs2 in
                      FStar_List.append uu____14150 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14174 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14174 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___135_14190 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___135_14190.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___135_14190.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14217 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14217
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14236 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14312  ->
                        match uu____14312 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___136_14433 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___136_14433.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___136_14433.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____14236 with
                | (rec_env,memos,uu____14646) ->
                    let uu____14699 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____15010 =
                               let uu____15017 =
                                 let uu____15018 =
                                   let uu____15049 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15049, false) in
                                 Clos uu____15018 in
                               (FStar_Pervasives_Native.None, uu____15017) in
                             uu____15010 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15159  ->
                     let uu____15160 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15160);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15182 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15184::uu____15185 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15190) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15191 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15222 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15236 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15236
                              | uu____15247 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15251 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15277 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15295 ->
                    let uu____15312 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains CheckNoUvars) in
                    if uu____15312
                    then
                      let uu____15313 =
                        let uu____15314 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____15315 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15314 uu____15315 in
                      failwith uu____15313
                    else rebuild cfg env stack t2
                | uu____15317 -> norm cfg env stack t2))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____15326 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15326 in
            let uu____15327 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15327 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15340  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15351  ->
                      let uu____15352 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15353 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15352
                        uu____15353);
                 (let t1 =
                    let uu____15355 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15357 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15357) in
                    if uu____15355
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t in
                  let n1 = FStar_List.length us in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack with
                    | (UnivArgs (us',uu____15367))::stack1 ->
                        ((let uu____15376 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug cfg.tcenv)
                              (FStar_Options.Other "univ_norm") in
                          if uu____15376
                          then
                            FStar_List.iter
                              (fun x  ->
                                 let uu____15380 =
                                   FStar_Syntax_Print.univ_to_string x in
                                 FStar_Util.print1 "Univ (normalizer) %s\n"
                                   uu____15380) us'
                          else ());
                         (let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env) in
                          norm cfg env1 stack1 t1))
                    | uu____15429 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15432 ->
                        let uu____15435 =
                          let uu____15436 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15436 in
                        failwith uu____15435
                  else norm cfg env stack t1))
and reduce_impure_comp:
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t in
              let stack1 = (Cfg cfg) :: stack in
              let cfg1 =
                let uu____15457 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15457
                then
                  let uu___137_15458 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___137_15458.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___137_15458.primitive_steps);
                    strong = (uu___137_15458.strong);
                    memoize_lazy = (uu___137_15458.memoize_lazy);
                    normalize_pure_lets =
                      (uu___137_15458.normalize_pure_lets)
                  }
                else
                  (let uu___138_15460 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___138_15460.tcenv);
                     delta_level = (uu___138_15460.delta_level);
                     primitive_steps = (uu___138_15460.primitive_steps);
                     strong = (uu___138_15460.strong);
                     memoize_lazy = (uu___138_15460.memoize_lazy);
                     normalize_pure_lets =
                       (uu___138_15460.normalize_pure_lets)
                   }) in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1
and do_reify_monadic:
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head0 = head1 in
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____15490  ->
                     let uu____15491 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15492 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15491
                       uu____15492);
                (let uu____15493 =
                   let uu____15494 = FStar_Syntax_Subst.compress head2 in
                   uu____15494.FStar_Syntax_Syntax.n in
                 match uu____15493 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15512 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15512 with
                      | (uu____15513,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15519 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15527 =
                                   let uu____15528 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15528.FStar_Syntax_Syntax.n in
                                 match uu____15527 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15534,uu____15535))
                                     ->
                                     let uu____15544 =
                                       let uu____15545 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15545.FStar_Syntax_Syntax.n in
                                     (match uu____15544 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15551,msrc,uu____15553))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15562 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15562
                                      | uu____15563 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15564 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15565 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15565 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___139_15570 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___139_15570.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___139_15570.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___139_15570.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___139_15570.FStar_Syntax_Syntax.lbattrs)
                                      } in
                                    let uu____15571 = FStar_List.tl stack in
                                    let uu____15572 =
                                      let uu____15573 =
                                        let uu____15576 =
                                          let uu____15577 =
                                            let uu____15590 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15590) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15577 in
                                        FStar_Syntax_Syntax.mk uu____15576 in
                                      uu____15573
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15571 uu____15572
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15606 =
                                      let uu____15607 = is_return body in
                                      match uu____15607 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15611;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15612;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15617 -> false in
                                    if uu____15606
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos in
                                       let head3 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         } in
                                       let body2 =
                                         let uu____15640 =
                                           let uu____15643 =
                                             let uu____15644 =
                                               let uu____15661 =
                                                 let uu____15664 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15664] in
                                               (uu____15661, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15644 in
                                           FStar_Syntax_Syntax.mk uu____15643 in
                                         uu____15640
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15680 =
                                           let uu____15681 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15681.FStar_Syntax_Syntax.n in
                                         match uu____15680 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15687::uu____15688::[])
                                             ->
                                             let uu____15695 =
                                               let uu____15698 =
                                                 let uu____15699 =
                                                   let uu____15706 =
                                                     let uu____15709 =
                                                       let uu____15710 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15710 in
                                                     let uu____15711 =
                                                       let uu____15714 =
                                                         let uu____15715 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15715 in
                                                       [uu____15714] in
                                                     uu____15709 ::
                                                       uu____15711 in
                                                   (bind1, uu____15706) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15699 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15698 in
                                             uu____15695
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15723 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15729 =
                                           let uu____15732 =
                                             let uu____15733 =
                                               let uu____15748 =
                                                 let uu____15751 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15752 =
                                                   let uu____15755 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15756 =
                                                     let uu____15759 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15760 =
                                                       let uu____15763 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15764 =
                                                         let uu____15767 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15768 =
                                                           let uu____15771 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15771] in
                                                         uu____15767 ::
                                                           uu____15768 in
                                                       uu____15763 ::
                                                         uu____15764 in
                                                     uu____15759 ::
                                                       uu____15760 in
                                                   uu____15755 :: uu____15756 in
                                                 uu____15751 :: uu____15752 in
                                               (bind_inst, uu____15748) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15733 in
                                           FStar_Syntax_Syntax.mk uu____15732 in
                                         uu____15729
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15783  ->
                                            let uu____15784 =
                                              FStar_Syntax_Print.term_to_string
                                                head0 in
                                            let uu____15785 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15784 uu____15785);
                                       (let uu____15786 = FStar_List.tl stack in
                                        norm cfg env uu____15786 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15810 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15810 with
                      | (uu____15811,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15846 =
                                  let uu____15847 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15847.FStar_Syntax_Syntax.n in
                                match uu____15846 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15853) -> t2
                                | uu____15858 -> head3 in
                              let uu____15859 =
                                let uu____15860 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15860.FStar_Syntax_Syntax.n in
                              match uu____15859 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15866 -> FStar_Pervasives_Native.None in
                            let uu____15867 = maybe_extract_fv head3 in
                            match uu____15867 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15877 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15877
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15882 = maybe_extract_fv head4 in
                                  match uu____15882 with
                                  | FStar_Pervasives_Native.Some uu____15887
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15888 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15893 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15908 =
                              match uu____15908 with
                              | (e,q) ->
                                  let uu____15915 =
                                    let uu____15916 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15916.FStar_Syntax_Syntax.n in
                                  (match uu____15915 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15931 -> false) in
                            let uu____15932 =
                              let uu____15933 =
                                let uu____15940 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15940 :: args in
                              FStar_Util.for_some is_arg_impure uu____15933 in
                            if uu____15932
                            then
                              let uu____15945 =
                                let uu____15946 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15946 in
                              failwith uu____15945
                            else ());
                           (let uu____15948 = maybe_unfold_action head_app in
                            match uu____15948 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args)) in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body in
                                (log cfg
                                   (fun uu____15989  ->
                                      let uu____15990 =
                                        FStar_Syntax_Print.term_to_string
                                          head0 in
                                      let uu____15991 =
                                        FStar_Syntax_Print.term_to_string
                                          body1 in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15990 uu____15991);
                                 (let uu____15992 = FStar_List.tl stack in
                                  norm cfg env uu____15992 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15994) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16018 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____16018 in
                     (log cfg
                        (fun uu____16022  ->
                           let uu____16023 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16023);
                      (let uu____16024 = FStar_List.tl stack in
                       norm cfg env uu____16024 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____16026) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16151  ->
                               match uu____16151 with
                               | (pat,wopt,tm) ->
                                   let uu____16199 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____16199))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16231 = FStar_List.tl stack in
                     norm cfg env uu____16231 tm
                 | uu____16232 -> fallback ())
and reify_lift:
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv in
            log cfg
              (fun uu____16246  ->
                 let uu____16247 = FStar_Ident.string_of_lid msrc in
                 let uu____16248 = FStar_Ident.string_of_lid mtgt in
                 let uu____16249 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16247
                   uu____16248 uu____16249);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16251 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16251 with
               | (uu____16252,return_repr) ->
                   let return_inst =
                     let uu____16261 =
                       let uu____16262 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16262.FStar_Syntax_Syntax.n in
                     match uu____16261 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16268::[]) ->
                         let uu____16275 =
                           let uu____16278 =
                             let uu____16279 =
                               let uu____16286 =
                                 let uu____16289 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16289] in
                               (return_tm, uu____16286) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16279 in
                           FStar_Syntax_Syntax.mk uu____16278 in
                         uu____16275 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16297 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16300 =
                     let uu____16303 =
                       let uu____16304 =
                         let uu____16319 =
                           let uu____16322 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16323 =
                             let uu____16326 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16326] in
                           uu____16322 :: uu____16323 in
                         (return_inst, uu____16319) in
                       FStar_Syntax_Syntax.Tm_app uu____16304 in
                     FStar_Syntax_Syntax.mk uu____16303 in
                   uu____16300 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16335 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16335 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16338 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16338
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16339;
                     FStar_TypeChecker_Env.mtarget = uu____16340;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16341;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____16356 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16356
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16357;
                     FStar_TypeChecker_Env.mtarget = uu____16358;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16359;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16383 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16384 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16383 t FStar_Syntax_Syntax.tun uu____16384)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____16440  ->
                   match uu____16440 with
                   | (a,imp) ->
                       let uu____16451 = norm cfg env [] a in
                       (uu____16451, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___140_16465 = comp in
            let uu____16466 =
              let uu____16467 =
                let uu____16476 = norm cfg env [] t in
                let uu____16477 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16476, uu____16477) in
              FStar_Syntax_Syntax.Total uu____16467 in
            {
              FStar_Syntax_Syntax.n = uu____16466;
              FStar_Syntax_Syntax.pos =
                (uu___140_16465.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___140_16465.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___141_16492 = comp in
            let uu____16493 =
              let uu____16494 =
                let uu____16503 = norm cfg env [] t in
                let uu____16504 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16503, uu____16504) in
              FStar_Syntax_Syntax.GTotal uu____16494 in
            {
              FStar_Syntax_Syntax.n = uu____16493;
              FStar_Syntax_Syntax.pos =
                (uu___141_16492.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___141_16492.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16556  ->
                      match uu____16556 with
                      | (a,i) ->
                          let uu____16567 = norm cfg env [] a in
                          (uu____16567, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_16578  ->
                      match uu___88_16578 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16582 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16582
                      | f -> f)) in
            let uu___142_16586 = comp in
            let uu____16587 =
              let uu____16588 =
                let uu___143_16589 = ct in
                let uu____16590 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16591 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16594 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16590;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___143_16589.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16591;
                  FStar_Syntax_Syntax.effect_args = uu____16594;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16588 in
            {
              FStar_Syntax_Syntax.n = uu____16587;
              FStar_Syntax_Syntax.pos =
                (uu___142_16586.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___142_16586.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16605  ->
        match uu____16605 with
        | (x,imp) ->
            let uu____16608 =
              let uu___144_16609 = x in
              let uu____16610 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___144_16609.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___144_16609.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16610
              } in
            (uu____16608, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16616 =
          FStar_List.fold_left
            (fun uu____16634  ->
               fun b  ->
                 match uu____16634 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16616 with | (nbs,uu____16674) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____16690 =
              let uu___145_16691 = rc in
              let uu____16692 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___145_16691.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16692;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___145_16691.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16690
        | uu____16699 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16712  ->
               let uu____16713 = FStar_Syntax_Print.tag_of_term t in
               let uu____16714 = FStar_Syntax_Print.term_to_string t in
               let uu____16715 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16722 =
                 let uu____16723 =
                   let uu____16726 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16726 in
                 stack_to_string uu____16723 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16713 uu____16714 uu____16715 uu____16722);
          (let t1 = maybe_simplify cfg env stack t in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16756 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16756
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16758 =
                     let uu____16759 =
                       let uu____16760 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16760 in
                     FStar_Util.string_of_int uu____16759 in
                   let uu____16765 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16766 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16758 uu____16765 uu____16766
                 else ());
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____16820  ->
                     let uu____16821 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16821);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____16857 =
                 let uu___146_16858 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___146_16858.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___146_16858.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16857
           | (Arg (Univ uu____16859,uu____16860,uu____16861))::uu____16862 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16865,uu____16866))::uu____16867 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____16883),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16936  ->
                     let uu____16937 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16937);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1 in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____16947 = FStar_ST.op_Bang m in
                   match uu____16947 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1 in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____17084,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1 in
               let fallback msg uu____17131 =
                 log cfg
                   (fun uu____17135  ->
                      let uu____17136 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____17136);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t2) in
               let uu____17140 =
                 let uu____17141 = FStar_Syntax_Subst.compress t1 in
                 uu____17141.FStar_Syntax_Syntax.n in
               (match uu____17140 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____17168 = closure_as_term cfg env1 ty in
                      reify_lift cfg t2 msrc mtgt uu____17168 in
                    (log cfg
                       (fun uu____17172  ->
                          let uu____17173 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____17173);
                     (let uu____17174 = FStar_List.tl stack in
                      norm cfg env1 uu____17174 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____17175);
                       FStar_Syntax_Syntax.pos = uu____17176;
                       FStar_Syntax_Syntax.vars = uu____17177;_},(e,uu____17179)::[])
                    -> norm cfg env1 stack' e
                | uu____17208 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17228  ->
                     let uu____17229 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17229);
                (let scrutinee = t1 in
                 let norm_and_rebuild_match uu____17234 =
                   log cfg
                     (fun uu____17239  ->
                        let uu____17240 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17241 =
                          let uu____17242 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17259  ->
                                    match uu____17259 with
                                    | (p,uu____17269,uu____17270) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17242
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17240 uu____17241);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_17287  ->
                                match uu___89_17287 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17288 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___147_17292 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___147_17292.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___147_17292.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___147_17292.memoize_lazy);
                        normalize_pure_lets =
                          (uu___147_17292.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17324 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17345 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17405  ->
                                    fun uu____17406  ->
                                      match (uu____17405, uu____17406) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17497 = norm_pat env3 p1 in
                                          (match uu____17497 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17345 with
                           | (pats1,env3) ->
                               ((let uu___148_17579 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___148_17579.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___149_17598 = x in
                            let uu____17599 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___149_17598.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___149_17598.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17599
                            } in
                          ((let uu___150_17613 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___150_17613.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___151_17624 = x in
                            let uu____17625 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___151_17624.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___151_17624.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17625
                            } in
                          ((let uu___152_17639 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___152_17639.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___153_17655 = x in
                            let uu____17656 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___153_17655.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___153_17655.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17656
                            } in
                          let t3 = norm_or_whnf env2 t2 in
                          ((let uu___154_17663 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___154_17663.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17673 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17687 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17687 with
                                  | (p,wopt,e) ->
                                      let uu____17707 = norm_pat env1 p in
                                      (match uu____17707 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17732 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17732 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17738 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17738) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17748) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17753 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17754;
                         FStar_Syntax_Syntax.fv_delta = uu____17755;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17756;
                         FStar_Syntax_Syntax.fv_delta = uu____17757;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17758);_}
                       -> true
                   | uu____17765 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____17910 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17910 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17997 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18036 ->
                                 let uu____18037 =
                                   let uu____18038 = is_cons head1 in
                                   Prims.op_Negation uu____18038 in
                                 FStar_Util.Inr uu____18037)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18063 =
                              let uu____18064 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18064.FStar_Syntax_Syntax.n in
                            (match uu____18063 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18082 ->
                                 let uu____18083 =
                                   let uu____18084 = is_cons head1 in
                                   Prims.op_Negation uu____18084 in
                                 FStar_Util.Inr uu____18083))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____18153)::rest_a,(p1,uu____18156)::rest_p) ->
                       let uu____18200 = matches_pat t2 p1 in
                       (match uu____18200 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18249 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18355 = matches_pat scrutinee1 p1 in
                       (match uu____18355 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18395  ->
                                  let uu____18396 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18397 =
                                    let uu____18398 =
                                      FStar_List.map
                                        (fun uu____18408  ->
                                           match uu____18408 with
                                           | (uu____18413,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s in
                                    FStar_All.pipe_right uu____18398
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18396 uu____18397);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18444  ->
                                       match uu____18444 with
                                       | (bv,t2) ->
                                           let uu____18467 =
                                             let uu____18474 =
                                               let uu____18477 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18477 in
                                             let uu____18478 =
                                               let uu____18479 =
                                                 let uu____18510 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2)) in
                                                 ([], t2, uu____18510, false) in
                                               Clos uu____18479 in
                                             (uu____18474, uu____18478) in
                                           uu____18467 :: env2) env1 s in
                              let uu____18627 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18627))) in
                 let uu____18628 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18628
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___90_18649  ->
                match uu___90_18649 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18653 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18659 -> d in
      let uu____18662 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18664 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations) in
           Prims.op_Negation uu____18664) in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18662
      }
let normalize_with_primitive_steps:
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e in
          let c1 =
            let uu___155_18689 = config s e in
            {
              steps = (uu___155_18689.steps);
              tcenv = (uu___155_18689.tcenv);
              delta_level = (uu___155_18689.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___155_18689.strong);
              memoize_lazy = (uu___155_18689.memoize_lazy);
              normalize_pure_lets = (uu___155_18689.normalize_pure_lets)
            } in
          norm c1 [] [] t
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____18714 = config s e in norm_comp uu____18714 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18727 = config [] env in norm_universe uu____18727 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env in
      let non_info t =
        let uu____18745 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18745 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18752 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___156_18771 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___156_18771.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___156_18771.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18778 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18778
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___157_18787 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___157_18787.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___157_18787.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___157_18787.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___158_18789 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___158_18789.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___158_18789.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___158_18789.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___158_18789.FStar_Syntax_Syntax.flags)
                  } in
            let uu___159_18790 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___159_18790.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___159_18790.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18792 -> c
let ghost_to_pure_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____18804 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18804 in
      let uu____18811 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18811
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18815  ->
                 let uu____18816 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18816)
        | FStar_Pervasives_Native.None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____18833 =
                let uu____18838 =
                  let uu____18839 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18839 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18838) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18833);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18850 = config [AllowUnboundUniverses] env in
          norm_comp uu____18850 [] c
        with
        | e ->
            ((let uu____18863 =
                let uu____18868 =
                  let uu____18869 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18869 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18868) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18863);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____18906 =
                     let uu____18907 =
                       let uu____18914 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18914) in
                     FStar_Syntax_Syntax.Tm_refine uu____18907 in
                   mk uu____18906 t01.FStar_Syntax_Syntax.pos
               | uu____18919 -> t2)
          | uu____18920 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____18960 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18960 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18989 ->
                 let uu____18996 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18996 with
                  | (actuals,uu____19006,uu____19007) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19021 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19021 with
                         | (binders,args) ->
                             let uu____19038 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19038
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____19046 ->
          let uu____19047 = FStar_Syntax_Util.head_and_args t in
          (match uu____19047 with
           | (head1,args) ->
               let uu____19084 =
                 let uu____19085 = FStar_Syntax_Subst.compress head1 in
                 uu____19085.FStar_Syntax_Syntax.n in
               (match uu____19084 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19088,thead) ->
                    let uu____19114 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19114 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19156 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___164_19164 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___164_19164.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___164_19164.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___164_19164.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___164_19164.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___164_19164.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___164_19164.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___164_19164.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___164_19164.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___164_19164.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___164_19164.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___164_19164.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___164_19164.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___164_19164.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___164_19164.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___164_19164.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___164_19164.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___164_19164.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___164_19164.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___164_19164.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___164_19164.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___164_19164.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___164_19164.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___164_19164.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___164_19164.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___164_19164.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___164_19164.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___164_19164.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___164_19164.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___164_19164.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___164_19164.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___164_19164.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___164_19164.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19156 with
                            | (uu____19165,ty,uu____19167) ->
                                eta_expand_with_type env t ty))
                | uu____19168 ->
                    let uu____19169 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___165_19177 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___165_19177.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___165_19177.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___165_19177.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___165_19177.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___165_19177.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___165_19177.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___165_19177.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___165_19177.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___165_19177.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___165_19177.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___165_19177.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___165_19177.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___165_19177.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___165_19177.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___165_19177.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___165_19177.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___165_19177.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___165_19177.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___165_19177.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___165_19177.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___165_19177.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___165_19177.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___165_19177.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___165_19177.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___165_19177.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___165_19177.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___165_19177.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___165_19177.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___165_19177.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___165_19177.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___165_19177.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___165_19177.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19169 with
                     | (uu____19178,ty,uu____19180) ->
                         eta_expand_with_type env t ty)))
let rec elim_delayed_subst_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___166_19237 = x in
      let uu____19238 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___166_19237.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___166_19237.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____19238
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____19241 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____19266 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____19267 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____19268 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____19269 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____19276 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____19277 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___167_19305 = rc in
          let uu____19306 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____19313 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___167_19305.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____19306;
            FStar_Syntax_Syntax.residual_flags = uu____19313
          } in
        let uu____19316 =
          let uu____19317 =
            let uu____19334 = elim_delayed_subst_binders bs in
            let uu____19341 = elim_delayed_subst_term t2 in
            let uu____19342 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____19334, uu____19341, uu____19342) in
          FStar_Syntax_Syntax.Tm_abs uu____19317 in
        mk1 uu____19316
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____19371 =
          let uu____19372 =
            let uu____19385 = elim_delayed_subst_binders bs in
            let uu____19392 = elim_delayed_subst_comp c in
            (uu____19385, uu____19392) in
          FStar_Syntax_Syntax.Tm_arrow uu____19372 in
        mk1 uu____19371
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____19405 =
          let uu____19406 =
            let uu____19413 = elim_bv bv in
            let uu____19414 = elim_delayed_subst_term phi in
            (uu____19413, uu____19414) in
          FStar_Syntax_Syntax.Tm_refine uu____19406 in
        mk1 uu____19405
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____19437 =
          let uu____19438 =
            let uu____19453 = elim_delayed_subst_term t2 in
            let uu____19454 = elim_delayed_subst_args args in
            (uu____19453, uu____19454) in
          FStar_Syntax_Syntax.Tm_app uu____19438 in
        mk1 uu____19437
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___168_19518 = p in
              let uu____19519 =
                let uu____19520 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____19520 in
              {
                FStar_Syntax_Syntax.v = uu____19519;
                FStar_Syntax_Syntax.p =
                  (uu___168_19518.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___169_19522 = p in
              let uu____19523 =
                let uu____19524 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____19524 in
              {
                FStar_Syntax_Syntax.v = uu____19523;
                FStar_Syntax_Syntax.p =
                  (uu___169_19522.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___170_19531 = p in
              let uu____19532 =
                let uu____19533 =
                  let uu____19540 = elim_bv x in
                  let uu____19541 = elim_delayed_subst_term t0 in
                  (uu____19540, uu____19541) in
                FStar_Syntax_Syntax.Pat_dot_term uu____19533 in
              {
                FStar_Syntax_Syntax.v = uu____19532;
                FStar_Syntax_Syntax.p =
                  (uu___170_19531.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___171_19560 = p in
              let uu____19561 =
                let uu____19562 =
                  let uu____19575 =
                    FStar_List.map
                      (fun uu____19598  ->
                         match uu____19598 with
                         | (x,b) ->
                             let uu____19611 = elim_pat x in (uu____19611, b))
                      pats in
                  (fv, uu____19575) in
                FStar_Syntax_Syntax.Pat_cons uu____19562 in
              {
                FStar_Syntax_Syntax.v = uu____19561;
                FStar_Syntax_Syntax.p =
                  (uu___171_19560.FStar_Syntax_Syntax.p)
              }
          | uu____19624 -> p in
        let elim_branch uu____19646 =
          match uu____19646 with
          | (pat,wopt,t3) ->
              let uu____19672 = elim_pat pat in
              let uu____19675 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____19678 = elim_delayed_subst_term t3 in
              (uu____19672, uu____19675, uu____19678) in
        let uu____19683 =
          let uu____19684 =
            let uu____19707 = elim_delayed_subst_term t2 in
            let uu____19708 = FStar_List.map elim_branch branches in
            (uu____19707, uu____19708) in
          FStar_Syntax_Syntax.Tm_match uu____19684 in
        mk1 uu____19683
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____19817 =
          match uu____19817 with
          | (tc,topt) ->
              let uu____19852 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____19862 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____19862
                | FStar_Util.Inr c ->
                    let uu____19864 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____19864 in
              let uu____19865 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____19852, uu____19865) in
        let uu____19874 =
          let uu____19875 =
            let uu____19902 = elim_delayed_subst_term t2 in
            let uu____19903 = elim_ascription a in
            (uu____19902, uu____19903, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____19875 in
        mk1 uu____19874
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___172_19948 = lb in
          let uu____19949 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____19952 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___172_19948.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___172_19948.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____19949;
            FStar_Syntax_Syntax.lbeff =
              (uu___172_19948.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____19952;
            FStar_Syntax_Syntax.lbattrs =
              (uu___172_19948.FStar_Syntax_Syntax.lbattrs)
          } in
        let uu____19955 =
          let uu____19956 =
            let uu____19969 =
              let uu____19976 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____19976) in
            let uu____19985 = elim_delayed_subst_term t2 in
            (uu____19969, uu____19985) in
          FStar_Syntax_Syntax.Tm_let uu____19956 in
        mk1 uu____19955
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____20018 =
          let uu____20019 =
            let uu____20036 = elim_delayed_subst_term t2 in (uv, uu____20036) in
          FStar_Syntax_Syntax.Tm_uvar uu____20019 in
        mk1 uu____20018
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____20053 =
          let uu____20054 =
            let uu____20061 = elim_delayed_subst_term t2 in
            let uu____20062 = elim_delayed_subst_meta md in
            (uu____20061, uu____20062) in
          FStar_Syntax_Syntax.Tm_meta uu____20054 in
        mk1 uu____20053
and elim_delayed_subst_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_20069  ->
         match uu___91_20069 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____20073 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____20073
         | f -> f) flags1
and elim_delayed_subst_comp:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____20094 =
          let uu____20095 =
            let uu____20104 = elim_delayed_subst_term t in
            (uu____20104, uopt) in
          FStar_Syntax_Syntax.Total uu____20095 in
        mk1 uu____20094
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____20117 =
          let uu____20118 =
            let uu____20127 = elim_delayed_subst_term t in
            (uu____20127, uopt) in
          FStar_Syntax_Syntax.GTotal uu____20118 in
        mk1 uu____20117
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___173_20132 = ct in
          let uu____20133 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____20136 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____20145 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___173_20132.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___173_20132.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____20133;
            FStar_Syntax_Syntax.effect_args = uu____20136;
            FStar_Syntax_Syntax.flags = uu____20145
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and elim_delayed_subst_meta:
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata =
  fun uu___92_20148  ->
    match uu___92_20148 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____20160 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____20160
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____20193 =
          let uu____20200 = elim_delayed_subst_term t in (m, uu____20200) in
        FStar_Syntax_Syntax.Meta_monadic uu____20193
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____20208 =
          let uu____20217 = elim_delayed_subst_term t in
          (m1, m2, uu____20217) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____20208
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____20225 =
          let uu____20234 = elim_delayed_subst_term t in (d, s, uu____20234) in
        FStar_Syntax_Syntax.Meta_alien uu____20225
    | m -> m
and elim_delayed_subst_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.map
      (fun uu____20257  ->
         match uu____20257 with
         | (t,q) ->
             let uu____20268 = elim_delayed_subst_term t in (uu____20268, q))
      args
and elim_delayed_subst_binders:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    FStar_List.map
      (fun uu____20288  ->
         match uu____20288 with
         | (x,q) ->
             let uu____20299 =
               let uu___174_20300 = x in
               let uu____20301 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___174_20300.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___174_20300.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____20301
               } in
             (uu____20299, q)) bs
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____20377,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____20383,FStar_Util.Inl t) ->
                let uu____20389 =
                  let uu____20392 =
                    let uu____20393 =
                      let uu____20406 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____20406) in
                    FStar_Syntax_Syntax.Tm_arrow uu____20393 in
                  FStar_Syntax_Syntax.mk uu____20392 in
                uu____20389 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____20410 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____20410 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____20438 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____20493 ->
                    let uu____20494 =
                      let uu____20503 =
                        let uu____20504 = FStar_Syntax_Subst.compress t4 in
                        uu____20504.FStar_Syntax_Syntax.n in
                      (uu____20503, tc) in
                    (match uu____20494 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____20529) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____20566) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____20605,FStar_Util.Inl uu____20606) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____20629 -> failwith "Impossible") in
              (match uu____20438 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____20734 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____20734 with
          | (univ_names1,binders1,tc) ->
              let uu____20792 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20792)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____20827 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20827 with
          | (univ_names1,binders1,tc) ->
              let uu____20887 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20887)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20920 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20920 with
           | (univ_names1,binders1,typ1) ->
               let uu___175_20948 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___175_20948.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___175_20948.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___175_20948.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___175_20948.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___176_20969 = s in
          let uu____20970 =
            let uu____20971 =
              let uu____20980 = FStar_List.map (elim_uvars env) sigs in
              (uu____20980, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20971 in
          {
            FStar_Syntax_Syntax.sigel = uu____20970;
            FStar_Syntax_Syntax.sigrng =
              (uu___176_20969.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___176_20969.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___176_20969.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___176_20969.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20997 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20997 with
           | (univ_names1,uu____21015,typ1) ->
               let uu___177_21029 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___177_21029.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___177_21029.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___177_21029.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___177_21029.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____21035 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____21035 with
           | (univ_names1,uu____21053,typ1) ->
               let uu___178_21067 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___178_21067.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___178_21067.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___178_21067.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___178_21067.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____21101 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____21101 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____21124 =
                            let uu____21125 =
                              let uu____21126 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____21126 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____21125 in
                          elim_delayed_subst_term uu____21124 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___179_21129 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___179_21129.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___179_21129.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___179_21129.FStar_Syntax_Syntax.lbattrs)
                        })) in
          let uu___180_21130 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___180_21130.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___180_21130.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___180_21130.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___180_21130.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___181_21142 = s in
          let uu____21143 =
            let uu____21144 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____21144 in
          {
            FStar_Syntax_Syntax.sigel = uu____21143;
            FStar_Syntax_Syntax.sigrng =
              (uu___181_21142.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___181_21142.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___181_21142.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___181_21142.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____21148 = elim_uvars_aux_t env us [] t in
          (match uu____21148 with
           | (us1,uu____21166,t1) ->
               let uu___182_21180 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___182_21180.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___182_21180.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___182_21180.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___182_21180.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21181 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21183 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____21183 with
           | (univs1,binders,signature) ->
               let uu____21211 =
                 let uu____21220 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____21220 with
                 | (univs_opening,univs2) ->
                     let uu____21247 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____21247) in
               (match uu____21211 with
                | (univs_opening,univs_closing) ->
                    let uu____21264 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____21270 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____21271 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____21270, uu____21271) in
                    (match uu____21264 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____21293 =
                           match uu____21293 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____21311 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____21311 with
                                | (us1,t1) ->
                                    let uu____21322 =
                                      let uu____21327 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____21334 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____21327, uu____21334) in
                                    (match uu____21322 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____21347 =
                                           let uu____21352 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____21361 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____21352, uu____21361) in
                                         (match uu____21347 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____21377 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____21377 in
                                              let uu____21378 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____21378 with
                                               | (uu____21399,uu____21400,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____21415 =
                                                       let uu____21416 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____21416 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____21415 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____21421 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____21421 with
                           | (uu____21434,uu____21435,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____21495 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____21512 =
                               let uu____21513 =
                                 FStar_Syntax_Subst.compress body in
                               uu____21513.FStar_Syntax_Syntax.n in
                             match uu____21512 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____21572 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____21601 =
                               let uu____21602 =
                                 FStar_Syntax_Subst.compress t in
                               uu____21602.FStar_Syntax_Syntax.n in
                             match uu____21601 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____21623) ->
                                 let uu____21644 = destruct_action_body body in
                                 (match uu____21644 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____21689 ->
                                 let uu____21690 = destruct_action_body t in
                                 (match uu____21690 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____21739 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____21739 with
                           | (action_univs,t) ->
                               let uu____21748 = destruct_action_typ_templ t in
                               (match uu____21748 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___183_21789 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___183_21789.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___183_21789.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___184_21791 = ed in
                           let uu____21792 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21793 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21794 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21795 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21796 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21797 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21798 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21799 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21800 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21801 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21802 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21803 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21804 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21805 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___184_21791.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___184_21791.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21792;
                             FStar_Syntax_Syntax.bind_wp = uu____21793;
                             FStar_Syntax_Syntax.if_then_else = uu____21794;
                             FStar_Syntax_Syntax.ite_wp = uu____21795;
                             FStar_Syntax_Syntax.stronger = uu____21796;
                             FStar_Syntax_Syntax.close_wp = uu____21797;
                             FStar_Syntax_Syntax.assert_p = uu____21798;
                             FStar_Syntax_Syntax.assume_p = uu____21799;
                             FStar_Syntax_Syntax.null_wp = uu____21800;
                             FStar_Syntax_Syntax.trivial = uu____21801;
                             FStar_Syntax_Syntax.repr = uu____21802;
                             FStar_Syntax_Syntax.return_repr = uu____21803;
                             FStar_Syntax_Syntax.bind_repr = uu____21804;
                             FStar_Syntax_Syntax.actions = uu____21805
                           } in
                         let uu___185_21808 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___185_21808.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___185_21808.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___185_21808.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___185_21808.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_21825 =
            match uu___93_21825 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21852 = elim_uvars_aux_t env us [] t in
                (match uu____21852 with
                 | (us1,uu____21876,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___186_21895 = sub_eff in
            let uu____21896 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21899 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___186_21895.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___186_21895.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21896;
              FStar_Syntax_Syntax.lift = uu____21899
            } in
          let uu___187_21902 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___187_21902.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___187_21902.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___187_21902.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___187_21902.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____21912 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21912 with
           | (univ_names1,binders1,comp1) ->
               let uu___188_21946 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___188_21946.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___188_21946.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___188_21946.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___188_21946.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21957 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t