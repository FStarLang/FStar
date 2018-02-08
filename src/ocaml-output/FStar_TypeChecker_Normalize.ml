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
  fun uu___74_521  ->
    match uu___74_521 with
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
  fun uu___75_1401  ->
    match uu___75_1401 with
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
  fun uu___76_1507  ->
    match uu___76_1507 with | [] -> true | uu____1510 -> false
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
                 let uu____1703 =
                   let uu____1704 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1704 in
                 match uu____1703 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1722 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1731 ->
                   let uu____1732 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1732
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1738 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1747 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1756 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1763 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1763 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1780 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1780 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1788 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1796 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1796 with
                                  | (uu____1801,m) -> n1 <= m)) in
                        if uu____1788 then rest1 else us1
                    | uu____1806 -> us1)
               | uu____1811 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1815 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1815 in
        let uu____1818 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1818
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1820 = aux u in
           match uu____1820 with
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
          (fun uu____1924  ->
             let uu____1925 = FStar_Syntax_Print.tag_of_term t in
             let uu____1926 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1925
               uu____1926);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1933 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1935 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1960 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1961 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1962 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1963 ->
                  let uu____1980 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1980
                  then
                    let uu____1981 =
                      let uu____1982 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1983 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1982 uu____1983 in
                    failwith uu____1981
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1986 =
                    let uu____1987 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1987 in
                  mk uu____1986 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1994 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1994
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1996 = lookup_bvar env x in
                  (match uu____1996 with
                   | Univ uu____1999 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____2002,uu____2003) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2115 = closures_as_binders_delayed cfg env bs in
                  (match uu____2115 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2143 =
                         let uu____2144 =
                           let uu____2161 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2161) in
                         FStar_Syntax_Syntax.Tm_abs uu____2144 in
                       mk uu____2143 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2192 = closures_as_binders_delayed cfg env bs in
                  (match uu____2192 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2234 =
                    let uu____2245 =
                      let uu____2252 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2252] in
                    closures_as_binders_delayed cfg env uu____2245 in
                  (match uu____2234 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2270 =
                         let uu____2271 =
                           let uu____2278 =
                             let uu____2279 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2279
                               FStar_Pervasives_Native.fst in
                           (uu____2278, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2271 in
                       mk uu____2270 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2370 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2370
                    | FStar_Util.Inr c ->
                        let uu____2384 = close_comp cfg env c in
                        FStar_Util.Inr uu____2384 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2400 =
                    let uu____2401 =
                      let uu____2428 = closure_as_term_delayed cfg env t11 in
                      (uu____2428, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2401 in
                  mk uu____2400 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2479 =
                    let uu____2480 =
                      let uu____2487 = closure_as_term_delayed cfg env t' in
                      let uu____2490 =
                        let uu____2491 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2491 in
                      (uu____2487, uu____2490) in
                    FStar_Syntax_Syntax.Tm_meta uu____2480 in
                  mk uu____2479 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2551 =
                    let uu____2552 =
                      let uu____2559 = closure_as_term_delayed cfg env t' in
                      let uu____2562 =
                        let uu____2563 =
                          let uu____2570 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2570) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2563 in
                      (uu____2559, uu____2562) in
                    FStar_Syntax_Syntax.Tm_meta uu____2552 in
                  mk uu____2551 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2589 =
                    let uu____2590 =
                      let uu____2597 = closure_as_term_delayed cfg env t' in
                      let uu____2600 =
                        let uu____2601 =
                          let uu____2610 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2610) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2601 in
                      (uu____2597, uu____2600) in
                    FStar_Syntax_Syntax.Tm_meta uu____2590 in
                  mk uu____2589 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2623 =
                    let uu____2624 =
                      let uu____2631 = closure_as_term_delayed cfg env t' in
                      (uu____2631, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2624 in
                  mk uu____2623 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2671  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2690 =
                    let uu____2701 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2701
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2720 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___97_2732 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___97_2732.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___97_2732.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2720)) in
                  (match uu____2690 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___98_2748 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___98_2748.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___98_2748.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2759,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2818  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2843 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2843
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2863  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2885 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2885
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___99_2897 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___99_2897.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___99_2897.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___100_2898 = lb in
                    let uu____2899 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___100_2898.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___100_2898.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2899
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2929  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3018 =
                    match uu____3018 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3073 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3094 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3154  ->
                                        fun uu____3155  ->
                                          match (uu____3154, uu____3155) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3246 =
                                                norm_pat env3 p1 in
                                              (match uu____3246 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3094 with
                               | (pats1,env3) ->
                                   ((let uu___101_3328 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___101_3328.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___102_3347 = x in
                                let uu____3348 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3347.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3347.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3348
                                } in
                              ((let uu___103_3362 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3362.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___104_3373 = x in
                                let uu____3374 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___104_3373.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___104_3373.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3374
                                } in
                              ((let uu___105_3388 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___105_3388.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___106_3404 = x in
                                let uu____3405 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___106_3404.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___106_3404.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3405
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___107_3412 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___107_3412.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3415 = norm_pat env1 pat in
                        (match uu____3415 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3444 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3444 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3450 =
                    let uu____3451 =
                      let uu____3474 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3474) in
                    FStar_Syntax_Syntax.Tm_match uu____3451 in
                  mk uu____3450 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3560 -> closure_as_term cfg env t
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
        | uu____3586 ->
            FStar_List.map
              (fun uu____3603  ->
                 match uu____3603 with
                 | (x,imp) ->
                     let uu____3622 = closure_as_term_delayed cfg env x in
                     (uu____3622, imp)) args
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
        let uu____3636 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3685  ->
                  fun uu____3686  ->
                    match (uu____3685, uu____3686) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___108_3756 = b in
                          let uu____3757 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___108_3756.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___108_3756.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3757
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3636 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3850 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3863 = closure_as_term_delayed cfg env t in
                 let uu____3864 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3863 uu____3864
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3877 = closure_as_term_delayed cfg env t in
                 let uu____3878 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3877 uu____3878
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
                        (fun uu___77_3904  ->
                           match uu___77_3904 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3908 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3908
                           | f -> f)) in
                 let uu____3912 =
                   let uu___109_3913 = c1 in
                   let uu____3914 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3914;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___109_3913.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3912)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___78_3924  ->
            match uu___78_3924 with
            | FStar_Syntax_Syntax.DECREASES uu____3925 -> false
            | uu____3928 -> true))
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
                   (fun uu___79_3946  ->
                      match uu___79_3946 with
                      | FStar_Syntax_Syntax.DECREASES uu____3947 -> false
                      | uu____3950 -> true)) in
            let rc1 =
              let uu___110_3952 = rc in
              let uu____3953 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___110_3952.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3953;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3960 -> lopt
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
    let uu____4045 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4045 in
  let arg_as_bounded_int uu____4073 =
    match uu____4073 with
    | (a,uu____4085) ->
        let uu____4092 =
          let uu____4093 = FStar_Syntax_Subst.compress a in
          uu____4093.FStar_Syntax_Syntax.n in
        (match uu____4092 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4103;
                FStar_Syntax_Syntax.vars = uu____4104;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4106;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4107;_},uu____4108)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4147 =
               let uu____4152 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4152) in
             FStar_Pervasives_Native.Some uu____4147
         | uu____4157 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4197 = f a in FStar_Pervasives_Native.Some uu____4197
    | uu____4198 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4246 = f a0 a1 in FStar_Pervasives_Native.Some uu____4246
    | uu____4247 -> FStar_Pervasives_Native.None in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4289 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____4289)) a416 a417 a418 a419 a420 in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4338 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____4338)) a423 a424 a425 a426 a427 in
  let as_primitive_step uu____4362 =
    match uu____4362 with
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
                   let uu____4410 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4410)) a429 a430) in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4438 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4438)) a432
               a433 a434) in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4459 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4459)) a436
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
                       let uu____4487 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4487)) a439
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
                       let uu____4515 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4515))
               a443 a444 a445) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4623 =
          let uu____4632 = as_a a in
          let uu____4635 = as_b b in (uu____4632, uu____4635) in
        (match uu____4623 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4650 =
               let uu____4651 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4651 in
             FStar_Pervasives_Native.Some uu____4650
         | uu____4652 -> FStar_Pervasives_Native.None)
    | uu____4661 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4675 =
        let uu____4676 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4676 in
      mk uu____4675 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4686 =
      let uu____4689 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4689 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4686 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4721 =
      let uu____4722 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4722 in
    FStar_Syntax_Embeddings.embed_int rng uu____4721 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4740 = arg_as_string a1 in
        (match uu____4740 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4746 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4746 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4759 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4759
              | uu____4760 -> FStar_Pervasives_Native.None)
         | uu____4765 -> FStar_Pervasives_Native.None)
    | uu____4768 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4778 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4778 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4802 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4813 =
          let uu____4834 = arg_as_string fn in
          let uu____4837 = arg_as_int from_line in
          let uu____4840 = arg_as_int from_col in
          let uu____4843 = arg_as_int to_line in
          let uu____4846 = arg_as_int to_col in
          (uu____4834, uu____4837, uu____4840, uu____4843, uu____4846) in
        (match uu____4813 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4877 =
                 let uu____4878 = FStar_BigInt.to_int_fs from_l in
                 let uu____4879 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4878 uu____4879 in
               let uu____4880 =
                 let uu____4881 = FStar_BigInt.to_int_fs to_l in
                 let uu____4882 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4881 uu____4882 in
               FStar_Range.mk_range fn1 uu____4877 uu____4880 in
             let uu____4883 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4883
         | uu____4888 -> FStar_Pervasives_Native.None)
    | uu____4909 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4936)::(a1,uu____4938)::(a2,uu____4940)::[] ->
        let uu____4977 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4977 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4990 -> FStar_Pervasives_Native.None)
    | uu____4991 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5018)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5027 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5051 =
      let uu____5066 =
        let uu____5081 =
          let uu____5096 =
            let uu____5111 =
              let uu____5126 =
                let uu____5141 =
                  let uu____5156 =
                    let uu____5171 =
                      let uu____5186 =
                        let uu____5201 =
                          let uu____5216 =
                            let uu____5231 =
                              let uu____5246 =
                                let uu____5261 =
                                  let uu____5276 =
                                    let uu____5291 =
                                      let uu____5306 =
                                        let uu____5321 =
                                          let uu____5336 =
                                            let uu____5351 =
                                              let uu____5366 =
                                                let uu____5379 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5379,
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
                                              let uu____5386 =
                                                let uu____5401 =
                                                  let uu____5414 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5414,
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
                                                let uu____5421 =
                                                  let uu____5436 =
                                                    let uu____5451 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5451,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5460 =
                                                    let uu____5477 =
                                                      let uu____5492 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5492,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5501 =
                                                      let uu____5518 =
                                                        let uu____5537 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5537,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5518] in
                                                    uu____5477 :: uu____5501 in
                                                  uu____5436 :: uu____5460 in
                                                uu____5401 :: uu____5421 in
                                              uu____5366 :: uu____5386 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5351 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5336 in
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
                                          :: uu____5321 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____5306 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____5291 in
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
                                                        let uu____5754 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5754 y)) a466
                                                a467 a468)))
                                    :: uu____5276 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5261 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5246 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5231 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5216 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5201 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5186 in
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
                                          let uu____5921 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5921)) a470 a471 a472)))
                      :: uu____5171 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5947 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5947)) a474 a475 a476)))
                    :: uu____5156 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5973 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5973)) a478 a479 a480)))
                  :: uu____5141 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5999 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5999)) a482 a483 a484)))
                :: uu____5126 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5111 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5096 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5081 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5066 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5051 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6152 =
        let uu____6153 =
          let uu____6154 = FStar_Syntax_Syntax.as_arg c in [uu____6154] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6153 in
      uu____6152 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6204 =
                let uu____6217 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6217, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6233  ->
                                    fun uu____6234  ->
                                      match (uu____6233, uu____6234) with
                                      | ((int_to_t1,x),(uu____6253,y)) ->
                                          let uu____6263 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6263)) a486 a487 a488))) in
              let uu____6264 =
                let uu____6279 =
                  let uu____6292 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6292, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6308  ->
                                      fun uu____6309  ->
                                        match (uu____6308, uu____6309) with
                                        | ((int_to_t1,x),(uu____6328,y)) ->
                                            let uu____6338 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6338)) a490 a491 a492))) in
                let uu____6339 =
                  let uu____6354 =
                    let uu____6367 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6367, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6383  ->
                                        fun uu____6384  ->
                                          match (uu____6383, uu____6384) with
                                          | ((int_to_t1,x),(uu____6403,y)) ->
                                              let uu____6413 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____6413)) a494 a495 a496))) in
                  let uu____6414 =
                    let uu____6429 =
                      let uu____6442 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____6442, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6454  ->
                                        match uu____6454 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499))) in
                    [uu____6429] in
                  uu____6354 :: uu____6414 in
                uu____6279 :: uu____6339 in
              uu____6204 :: uu____6264)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6568 =
                let uu____6581 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6581, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6597  ->
                                    fun uu____6598  ->
                                      match (uu____6597, uu____6598) with
                                      | ((int_to_t1,x),(uu____6617,y)) ->
                                          let uu____6627 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6627)) a501 a502 a503))) in
              let uu____6628 =
                let uu____6643 =
                  let uu____6656 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6656, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6672  ->
                                      fun uu____6673  ->
                                        match (uu____6672, uu____6673) with
                                        | ((int_to_t1,x),(uu____6692,y)) ->
                                            let uu____6702 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6702)) a505 a506 a507))) in
                [uu____6643] in
              uu____6568 :: uu____6628)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6792)::(a1,uu____6794)::(a2,uu____6796)::[] ->
        let uu____6833 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6833 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_6839 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_6839.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_6839.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6843 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6843.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6843.FStar_Syntax_Syntax.vars)
                })
         | uu____6844 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6846)::uu____6847::(a1,uu____6849)::(a2,uu____6851)::[] ->
        let uu____6900 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6900 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_6906 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_6906.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_6906.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6910 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6910.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6910.FStar_Syntax_Syntax.vars)
                })
         | uu____6911 -> FStar_Pervasives_Native.None)
    | uu____6912 -> failwith "Unexpected number of arguments" in
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
      let uu____6931 =
        let uu____6932 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6932 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6931
    with | uu____6938 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6942 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6942) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7002  ->
           fun subst1  ->
             match uu____7002 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____7043,uu____7044)) ->
                      let uu____7103 = b in
                      (match uu____7103 with
                       | (bv,uu____7111) ->
                           let uu____7112 =
                             let uu____7113 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7113 in
                           if uu____7112
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7118 = unembed_binder term1 in
                              match uu____7118 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7125 =
                                      let uu___115_7126 = bv in
                                      let uu____7127 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___115_7126.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___115_7126.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7127
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7125 in
                                  let b_for_x =
                                    let uu____7131 =
                                      let uu____7138 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7138) in
                                    FStar_Syntax_Syntax.NT uu____7131 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___80_7147  ->
                                         match uu___80_7147 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7148,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7150;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7151;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7156 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7157 -> subst1)) env []
let reduce_primops:
  'Auu____7174 'Auu____7175 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7175) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7174 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7216 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7216
          then tm
          else
            (let uu____7218 = FStar_Syntax_Util.head_and_args tm in
             match uu____7218 with
             | (head1,args) ->
                 let uu____7255 =
                   let uu____7256 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7256.FStar_Syntax_Syntax.n in
                 (match uu____7255 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7260 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7260 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7277  ->
                                   let uu____7278 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7279 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7286 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7278 uu____7279 uu____7286);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7291  ->
                                   let uu____7292 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7292);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7295  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7297 =
                                 prim_step.interpretation psc args in
                               match uu____7297 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7303  ->
                                         let uu____7304 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7304);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7310  ->
                                         let uu____7311 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7312 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7311 uu____7312);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7313 ->
                           (log_primops cfg
                              (fun uu____7317  ->
                                 let uu____7318 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7318);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7322  ->
                            let uu____7323 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7323);
                       (match args with
                        | (a1,uu____7325)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7342 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7354  ->
                            let uu____7355 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7355);
                       (match args with
                        | (t,uu____7357)::(r,uu____7359)::[] ->
                            let uu____7386 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7386 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___116_7390 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___116_7390.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___116_7390.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7393 -> tm))
                  | uu____7402 -> tm))
let reduce_equality:
  'Auu____7407 'Auu____7408 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7408) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7407 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___117_7446 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___117_7446.tcenv);
           delta_level = (uu___117_7446.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___117_7446.strong);
           memoize_lazy = (uu___117_7446.memoize_lazy);
           normalize_pure_lets = (uu___117_7446.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____7453 'Auu____7454 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7454) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7453 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7496 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7496
          then tm1
          else
            (let w t =
               let uu___118_7508 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___118_7508.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___118_7508.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7524;
                      FStar_Syntax_Syntax.vars = uu____7525;_},uu____7526)
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
                      FStar_Syntax_Syntax.pos = uu____7533;
                      FStar_Syntax_Syntax.vars = uu____7534;_},uu____7535)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7541 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7546 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7546
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7567 =
                 match uu____7567 with
                 | (t1,q) ->
                     let uu____7580 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7580 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7608 -> (t1, q)) in
               let uu____7617 = FStar_Syntax_Util.head_and_args t in
               match uu____7617 with
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
                         FStar_Syntax_Syntax.pos = uu____7714;
                         FStar_Syntax_Syntax.vars = uu____7715;_},uu____7716);
                    FStar_Syntax_Syntax.pos = uu____7717;
                    FStar_Syntax_Syntax.vars = uu____7718;_},args)
                 ->
                 let uu____7744 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7744
                 then
                   let uu____7745 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7745 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7800)::
                        (uu____7801,(arg,uu____7803))::[] ->
                        maybe_auto_squash arg
                    | (uu____7868,(arg,uu____7870))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7871)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7936)::uu____7937::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8000::(FStar_Pervasives_Native.Some (false
                                   ),uu____8001)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8064 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8080 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8080
                    then
                      let uu____8081 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8081 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8136)::uu____8137::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8200::(FStar_Pervasives_Native.Some (true
                                     ),uu____8201)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8264)::
                          (uu____8265,(arg,uu____8267))::[] ->
                          maybe_auto_squash arg
                      | (uu____8332,(arg,uu____8334))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8335)::[]
                          -> maybe_auto_squash arg
                      | uu____8400 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8416 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8416
                       then
                         let uu____8417 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8417 with
                         | uu____8472::(FStar_Pervasives_Native.Some (true
                                        ),uu____8473)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8536)::uu____8537::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8600)::
                             (uu____8601,(arg,uu____8603))::[] ->
                             maybe_auto_squash arg
                         | (uu____8668,(p,uu____8670))::(uu____8671,(q,uu____8673))::[]
                             ->
                             let uu____8738 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8738
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8740 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8756 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8756
                          then
                            let uu____8757 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8757 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8812)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8851)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8890 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8906 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8906
                             then
                               match args with
                               | (t,uu____8908)::[] ->
                                   let uu____8925 =
                                     let uu____8926 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8926.FStar_Syntax_Syntax.n in
                                   (match uu____8925 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8929::[],body,uu____8931) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8958 -> tm1)
                                    | uu____8961 -> tm1)
                               | (uu____8962,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8963))::
                                   (t,uu____8965)::[] ->
                                   let uu____9004 =
                                     let uu____9005 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9005.FStar_Syntax_Syntax.n in
                                   (match uu____9004 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9008::[],body,uu____9010) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9037 -> tm1)
                                    | uu____9040 -> tm1)
                               | uu____9041 -> tm1
                             else
                               (let uu____9051 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9051
                                then
                                  match args with
                                  | (t,uu____9053)::[] ->
                                      let uu____9070 =
                                        let uu____9071 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9071.FStar_Syntax_Syntax.n in
                                      (match uu____9070 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9074::[],body,uu____9076)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9103 -> tm1)
                                       | uu____9106 -> tm1)
                                  | (uu____9107,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9108))::(t,uu____9110)::[] ->
                                      let uu____9149 =
                                        let uu____9150 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9150.FStar_Syntax_Syntax.n in
                                      (match uu____9149 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9153::[],body,uu____9155)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9182 -> tm1)
                                       | uu____9185 -> tm1)
                                  | uu____9186 -> tm1
                                else
                                  (let uu____9196 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9196
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9197;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9198;_},uu____9199)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9216;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9217;_},uu____9218)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9235 -> tm1
                                   else
                                     (let uu____9245 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9245 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9265 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9275;
                    FStar_Syntax_Syntax.vars = uu____9276;_},args)
                 ->
                 let uu____9298 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9298
                 then
                   let uu____9299 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9299 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9354)::
                        (uu____9355,(arg,uu____9357))::[] ->
                        maybe_auto_squash arg
                    | (uu____9422,(arg,uu____9424))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9425)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9490)::uu____9491::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9554::(FStar_Pervasives_Native.Some (false
                                   ),uu____9555)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9618 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9634 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9634
                    then
                      let uu____9635 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9635 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9690)::uu____9691::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9754::(FStar_Pervasives_Native.Some (true
                                     ),uu____9755)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9818)::
                          (uu____9819,(arg,uu____9821))::[] ->
                          maybe_auto_squash arg
                      | (uu____9886,(arg,uu____9888))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9889)::[]
                          -> maybe_auto_squash arg
                      | uu____9954 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9970 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9970
                       then
                         let uu____9971 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9971 with
                         | uu____10026::(FStar_Pervasives_Native.Some (true
                                         ),uu____10027)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10090)::uu____10091::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10154)::
                             (uu____10155,(arg,uu____10157))::[] ->
                             maybe_auto_squash arg
                         | (uu____10222,(p,uu____10224))::(uu____10225,
                                                           (q,uu____10227))::[]
                             ->
                             let uu____10292 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10292
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10294 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10310 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10310
                          then
                            let uu____10311 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10311 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10366)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10405)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10444 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10460 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10460
                             then
                               match args with
                               | (t,uu____10462)::[] ->
                                   let uu____10479 =
                                     let uu____10480 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10480.FStar_Syntax_Syntax.n in
                                   (match uu____10479 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10483::[],body,uu____10485) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10512 -> tm1)
                                    | uu____10515 -> tm1)
                               | (uu____10516,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10517))::
                                   (t,uu____10519)::[] ->
                                   let uu____10558 =
                                     let uu____10559 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10559.FStar_Syntax_Syntax.n in
                                   (match uu____10558 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10562::[],body,uu____10564) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10591 -> tm1)
                                    | uu____10594 -> tm1)
                               | uu____10595 -> tm1
                             else
                               (let uu____10605 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10605
                                then
                                  match args with
                                  | (t,uu____10607)::[] ->
                                      let uu____10624 =
                                        let uu____10625 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10625.FStar_Syntax_Syntax.n in
                                      (match uu____10624 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10628::[],body,uu____10630)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10657 -> tm1)
                                       | uu____10660 -> tm1)
                                  | (uu____10661,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10662))::(t,uu____10664)::[] ->
                                      let uu____10703 =
                                        let uu____10704 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10704.FStar_Syntax_Syntax.n in
                                      (match uu____10703 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10707::[],body,uu____10709)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10736 -> tm1)
                                       | uu____10739 -> tm1)
                                  | uu____10740 -> tm1
                                else
                                  (let uu____10750 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10750
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10751;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10752;_},uu____10753)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10770;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10771;_},uu____10772)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10789 -> tm1
                                   else
                                     (let uu____10799 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10799 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10819 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____10834 -> tm1)
let maybe_simplify:
  'Auu____10841 'Auu____10842 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10842) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10841 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10885 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10885
           then
             let uu____10886 = FStar_Syntax_Print.term_to_string tm in
             let uu____10887 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10886 uu____10887
           else ());
          tm'
let is_norm_request:
  'Auu____10893 .
    FStar_Syntax_Syntax.term -> 'Auu____10893 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10906 =
        let uu____10913 =
          let uu____10914 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10914.FStar_Syntax_Syntax.n in
        (uu____10913, args) in
      match uu____10906 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10920::uu____10921::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10925::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10930::uu____10931::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10934 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___81_10945  ->
    match uu___81_10945 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10951 =
          let uu____10954 =
            let uu____10955 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10955 in
          [uu____10954] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10951
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10971 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10971) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11009 =
          let uu____11012 =
            let uu____11017 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____11017 s in
          FStar_All.pipe_right uu____11012 FStar_Util.must in
        FStar_All.pipe_right uu____11009 tr_norm_steps in
      match args with
      | uu____11042::(tm,uu____11044)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11067)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11082)::uu____11083::(tm,uu____11085)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11125 =
              let uu____11128 = full_norm steps in parse_steps uu____11128 in
            Beta :: uu____11125 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11137 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___82_11154  ->
    match uu___82_11154 with
    | (App
        (uu____11157,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11158;
                       FStar_Syntax_Syntax.vars = uu____11159;_},uu____11160,uu____11161))::uu____11162
        -> true
    | uu____11169 -> false
let firstn:
  'Auu____11175 .
    Prims.int ->
      'Auu____11175 Prims.list ->
        ('Auu____11175 Prims.list,'Auu____11175 Prims.list)
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
          (uu____11211,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11212;
                         FStar_Syntax_Syntax.vars = uu____11213;_},uu____11214,uu____11215))::uu____11216
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11223 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            (let uu____11365 =
               FStar_TypeChecker_Env.debug cfg.tcenv
                 (FStar_Options.Other "NormDelayed") in
             if uu____11365
             then
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____11366 ->
                   let uu____11391 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11391
               | uu____11392 -> ()
             else ());
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11401  ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               let uu____11403 = FStar_Syntax_Print.tag_of_term t2 in
               let uu____11404 = FStar_Syntax_Print.term_to_string t2 in
               let uu____11405 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11412 =
                 let uu____11413 =
                   let uu____11416 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11416 in
                 stack_to_string uu____11413 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11403 uu____11404 uu____11405 uu____11412);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11439 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11440 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11441;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11442;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11445;
                 FStar_Syntax_Syntax.fv_delta = uu____11446;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11447;
                 FStar_Syntax_Syntax.fv_delta = uu____11448;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11449);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11457 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11457 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11463  ->
                     let uu____11464 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11465 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11464 uu____11465);
                if b
                then
                  (let uu____11466 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11466 t1 fv)
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
                 let uu___119_11505 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___119_11505.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___119_11505.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11538 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11538) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___120_11546 = cfg in
                 let uu____11547 =
                   FStar_List.filter
                     (fun uu___83_11550  ->
                        match uu___83_11550 with
                        | UnfoldOnly uu____11551 -> false
                        | NoDeltaSteps  -> false
                        | uu____11554 -> true) cfg.steps in
                 {
                   steps = uu____11547;
                   tcenv = (uu___120_11546.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___120_11546.primitive_steps);
                   strong = (uu___120_11546.strong);
                   memoize_lazy = (uu___120_11546.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____11555 = get_norm_request (norm cfg' env []) args in
               (match uu____11555 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11571 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___84_11576  ->
                                match uu___84_11576 with
                                | UnfoldUntil uu____11577 -> true
                                | UnfoldOnly uu____11578 -> true
                                | uu____11581 -> false)) in
                      if uu____11571
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___121_11586 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___121_11586.tcenv);
                        delta_level;
                        primitive_steps = (uu___121_11586.primitive_steps);
                        strong = (uu___121_11586.strong);
                        memoize_lazy = (uu___121_11586.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11593 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11593
                      then
                        let uu____11596 =
                          let uu____11597 =
                            let uu____11602 = FStar_Util.now () in
                            (t1, uu____11602) in
                          Debug uu____11597 in
                        uu____11596 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11606 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11606
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11613 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11613
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11616 =
                      let uu____11623 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11623, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11616 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___85_11636  ->
                         match uu___85_11636 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11639 =
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
                 if uu____11639
                 then false
                 else
                   (let uu____11641 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___86_11648  ->
                              match uu___86_11648 with
                              | UnfoldOnly uu____11649 -> true
                              | UnfoldAttr uu____11652 -> true
                              | uu____11653 -> false)) in
                    match uu____11641 with
                    | FStar_Pervasives_Native.Some uu____11654 ->
                        let attr_eq a a' =
                          let uu____11662 = FStar_Syntax_Util.eq_tm a a' in
                          match uu____11662 with
                          | FStar_Syntax_Util.Equal  -> true
                          | uu____11663 -> false in
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
                                      let uu____11673 =
                                        FStar_TypeChecker_Env.lookup_attrs_of_lid
                                          cfg.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      (match uu____11673 with
                                       | FStar_Pervasives_Native.Some attrs
                                           ->
                                           acc ||
                                             (FStar_Util.for_some
                                                (attr_eq attr) attrs)
                                       | uu____11683 -> acc)
                                  | uu____11688 -> acc) false cfg.steps)
                    | uu____11689 -> should_delta) in
               (log cfg
                  (fun uu____11697  ->
                     let uu____11698 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11699 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11700 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11698 uu____11699 uu____11700);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11703 = lookup_bvar env x in
               (match uu____11703 with
                | Univ uu____11706 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11755 = FStar_ST.op_Bang r in
                      (match uu____11755 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11873  ->
                                 let uu____11874 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11875 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11874
                                   uu____11875);
                            (let uu____11876 =
                               let uu____11877 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11877.FStar_Syntax_Syntax.n in
                             match uu____11876 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11880 ->
                                 norm cfg env2 stack t'
                             | uu____11897 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11967)::uu____11968 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11977)::uu____11978 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11988,uu____11989))::stack_rest ->
                    (match c with
                     | Univ uu____11993 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12002 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12023  ->
                                    let uu____12024 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12024);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12064  ->
                                    let uu____12065 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12065);
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
                       (fun uu____12143  ->
                          let uu____12144 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12144);
                     norm cfg env stack1 t1)
                | (Debug uu____12145)::uu____12146 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12153 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12153
                    else
                      (let uu____12155 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12155 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12197  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12225 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12225
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12235 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12235)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12240 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12240.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12240.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12241 -> lopt in
                           (log cfg
                              (fun uu____12247  ->
                                 let uu____12248 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12248);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12257 = cfg in
                               {
                                 steps = (uu___123_12257.steps);
                                 tcenv = (uu___123_12257.tcenv);
                                 delta_level = (uu___123_12257.delta_level);
                                 primitive_steps =
                                   (uu___123_12257.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12257.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12257.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12268)::uu____12269 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12276 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12276
                    else
                      (let uu____12278 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12278 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12320  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12348 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12348
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12358 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12358)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12363 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12363.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12363.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12364 -> lopt in
                           (log cfg
                              (fun uu____12370  ->
                                 let uu____12371 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12371);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12380 = cfg in
                               {
                                 steps = (uu___123_12380.steps);
                                 tcenv = (uu___123_12380.tcenv);
                                 delta_level = (uu___123_12380.delta_level);
                                 primitive_steps =
                                   (uu___123_12380.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12380.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12380.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12391)::uu____12392 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12403 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12403
                    else
                      (let uu____12405 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12405 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12447  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12475 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12475
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12485 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12485)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12490 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12490.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12490.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12491 -> lopt in
                           (log cfg
                              (fun uu____12497  ->
                                 let uu____12498 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12498);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12507 = cfg in
                               {
                                 steps = (uu___123_12507.steps);
                                 tcenv = (uu___123_12507.tcenv);
                                 delta_level = (uu___123_12507.delta_level);
                                 primitive_steps =
                                   (uu___123_12507.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12507.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12507.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12518)::uu____12519 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12530 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12530
                    else
                      (let uu____12532 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12532 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12574  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12602 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12602
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12612 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12612)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12617 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12617.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12617.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12618 -> lopt in
                           (log cfg
                              (fun uu____12624  ->
                                 let uu____12625 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12625);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12634 = cfg in
                               {
                                 steps = (uu___123_12634.steps);
                                 tcenv = (uu___123_12634.tcenv);
                                 delta_level = (uu___123_12634.delta_level);
                                 primitive_steps =
                                   (uu___123_12634.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12634.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12634.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12645)::uu____12646 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12661 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12661
                    else
                      (let uu____12663 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12663 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12705  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12733 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12733
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12743 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12743)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12748 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12748.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12748.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12749 -> lopt in
                           (log cfg
                              (fun uu____12755  ->
                                 let uu____12756 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12756);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12765 = cfg in
                               {
                                 steps = (uu___123_12765.steps);
                                 tcenv = (uu___123_12765.tcenv);
                                 delta_level = (uu___123_12765.delta_level);
                                 primitive_steps =
                                   (uu___123_12765.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12765.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12765.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12776 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12776
                    else
                      (let uu____12778 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12778 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12820  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12848 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12848
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12858 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12858)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12863 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12863.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12863.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12864 -> lopt in
                           (log cfg
                              (fun uu____12870  ->
                                 let uu____12871 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12871);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12880 = cfg in
                               {
                                 steps = (uu___123_12880.steps);
                                 tcenv = (uu___123_12880.tcenv);
                                 delta_level = (uu___123_12880.delta_level);
                                 primitive_steps =
                                   (uu___123_12880.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12880.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12880.normalize_pure_lets)
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
                      (fun uu____12929  ->
                         fun stack1  ->
                           match uu____12929 with
                           | (a,aq) ->
                               let uu____12941 =
                                 let uu____12942 =
                                   let uu____12949 =
                                     let uu____12950 =
                                       let uu____12981 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12981, false) in
                                     Clos uu____12950 in
                                   (uu____12949, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12942 in
                               uu____12941 :: stack1) args) in
               (log cfg
                  (fun uu____13065  ->
                     let uu____13066 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13066);
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
                             ((let uu___124_13102 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___124_13102.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___124_13102.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13103 ->
                      let uu____13108 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13108)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13111 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13111 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13142 =
                          let uu____13143 =
                            let uu____13150 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___125_13152 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___125_13152.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___125_13152.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13150) in
                          FStar_Syntax_Syntax.Tm_refine uu____13143 in
                        mk uu____13142 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13171 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13171
               else
                 (let uu____13173 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13173 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13181 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13205  -> dummy :: env1) env) in
                        norm_comp cfg uu____13181 c1 in
                      let t2 =
                        let uu____13227 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13227 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               FStar_List.contains Unascribe cfg.steps ->
               norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13338)::uu____13339 ->
                    (log cfg
                       (fun uu____13350  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13351)::uu____13352 ->
                    (log cfg
                       (fun uu____13363  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13364,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13365;
                                   FStar_Syntax_Syntax.vars = uu____13366;_},uu____13367,uu____13368))::uu____13369
                    ->
                    (log cfg
                       (fun uu____13378  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13379)::uu____13380 ->
                    (log cfg
                       (fun uu____13391  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13392 ->
                    (log cfg
                       (fun uu____13395  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13399  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13416 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13416
                         | FStar_Util.Inr c ->
                             let uu____13424 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13424 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13437 =
                               let uu____13438 =
                                 let uu____13465 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13465, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13438 in
                             mk uu____13437 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13484 ->
                           let uu____13485 =
                             let uu____13486 =
                               let uu____13487 =
                                 let uu____13514 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13514, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13487 in
                             mk uu____13486 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13485))))
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
                         let uu____13624 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13624 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___126_13644 = cfg in
                               let uu____13645 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___126_13644.steps);
                                 tcenv = uu____13645;
                                 delta_level = (uu___126_13644.delta_level);
                                 primitive_steps =
                                   (uu___126_13644.primitive_steps);
                                 strong = (uu___126_13644.strong);
                                 memoize_lazy = (uu___126_13644.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___126_13644.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____13650 =
                                 let uu____13651 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13651 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13650 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___127_13654 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___127_13654.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___127_13654.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13655 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13655
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13666,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13667;
                               FStar_Syntax_Syntax.lbunivs = uu____13668;
                               FStar_Syntax_Syntax.lbtyp = uu____13669;
                               FStar_Syntax_Syntax.lbeff = uu____13670;
                               FStar_Syntax_Syntax.lbdef = uu____13671;_}::uu____13672),uu____13673)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13709 =
                 (let uu____13712 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13712) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13714 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13714))) in
               if uu____13709
               then
                 let binder =
                   let uu____13716 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13716 in
                 let env1 =
                   let uu____13726 =
                     let uu____13733 =
                       let uu____13734 =
                         let uu____13765 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13765,
                           false) in
                       Clos uu____13734 in
                     ((FStar_Pervasives_Native.Some binder), uu____13733) in
                   uu____13726 :: env in
                 (log cfg
                    (fun uu____13858  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if FStar_List.contains Weak cfg.steps
                 then
                   (log cfg
                      (fun uu____13862  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13863 = closure_as_term cfg env t1 in
                     rebuild cfg env stack uu____13863))
                 else
                   (let uu____13865 =
                      let uu____13870 =
                        let uu____13871 =
                          let uu____13872 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____13872
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____13871] in
                      FStar_Syntax_Subst.open_term uu____13870 body in
                    match uu____13865 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13881  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                          let lbname =
                            let x =
                              let uu____13889 = FStar_List.hd bs in
                              FStar_Pervasives_Native.fst uu____13889 in
                            FStar_Util.Inl
                              (let uu___128_13899 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___128_13899.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___128_13899.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }) in
                          log cfg
                            (fun uu____13902  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___129_13904 = lb in
                             let uu____13905 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___129_13904.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___129_13904.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13905
                             } in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13940  -> dummy :: env1) env) in
                           let stack1 = (Cfg cfg) :: stack in
                           let cfg1 =
                             let uu___130_13963 = cfg in
                             {
                               steps = (uu___130_13963.steps);
                               tcenv = (uu___130_13963.tcenv);
                               delta_level = (uu___130_13963.delta_level);
                               primitive_steps =
                                 (uu___130_13963.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___130_13963.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___130_13963.normalize_pure_lets)
                             } in
                           log cfg1
                             (fun uu____13966  ->
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
               let uu____13983 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13983 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14019 =
                               let uu___131_14020 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_14020.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_14020.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14019 in
                           let uu____14021 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14021 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14047 =
                                   FStar_List.map (fun uu____14063  -> dummy)
                                     lbs1 in
                                 let uu____14064 =
                                   let uu____14073 =
                                     FStar_List.map
                                       (fun uu____14093  -> dummy) xs1 in
                                   FStar_List.append uu____14073 env in
                                 FStar_List.append uu____14047 uu____14064 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14117 =
                                       let uu___132_14118 = rc in
                                       let uu____14119 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___132_14118.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14119;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___132_14118.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14117
                                 | uu____14126 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___133_14130 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___133_14130.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___133_14130.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14140 =
                        FStar_List.map (fun uu____14156  -> dummy) lbs2 in
                      FStar_List.append uu____14140 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14164 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14164 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___134_14180 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___134_14180.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___134_14180.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14207 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14207
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14226 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14302  ->
                        match uu____14302 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___135_14423 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___135_14423.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___135_14423.FStar_Syntax_Syntax.sort)
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
               (match uu____14226 with
                | (rec_env,memos,uu____14636) ->
                    let uu____14689 =
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
                             let uu____15000 =
                               let uu____15007 =
                                 let uu____15008 =
                                   let uu____15039 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15039, false) in
                                 Clos uu____15008 in
                               (FStar_Pervasives_Native.None, uu____15007) in
                             uu____15000 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15149  ->
                     let uu____15150 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15150);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15172 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15174::uu____15175 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15180) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15181 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15212 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15226 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15226
                              | uu____15237 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15241 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15267 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15285 ->
                    let uu____15302 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains CheckNoUvars) in
                    if uu____15302
                    then
                      let uu____15303 =
                        let uu____15304 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____15305 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15304 uu____15305 in
                      failwith uu____15303
                    else rebuild cfg env stack t2
                | uu____15307 -> norm cfg env stack t2))
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
              let uu____15316 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15316 in
            let uu____15317 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15317 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15330  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15341  ->
                      let uu____15342 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15343 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15342
                        uu____15343);
                 (let t1 =
                    let uu____15345 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15347 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15347) in
                    if uu____15345
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
                    | (UnivArgs (us',uu____15357))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15412 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15415 ->
                        let uu____15418 =
                          let uu____15419 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15419 in
                        failwith uu____15418
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
                let uu____15440 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15440
                then
                  let uu___136_15441 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___136_15441.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___136_15441.primitive_steps);
                    strong = (uu___136_15441.strong);
                    memoize_lazy = (uu___136_15441.memoize_lazy);
                    normalize_pure_lets =
                      (uu___136_15441.normalize_pure_lets)
                  }
                else
                  (let uu___137_15443 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___137_15443.tcenv);
                     delta_level = (uu___137_15443.delta_level);
                     primitive_steps = (uu___137_15443.primitive_steps);
                     strong = (uu___137_15443.strong);
                     memoize_lazy = (uu___137_15443.memoize_lazy);
                     normalize_pure_lets =
                       (uu___137_15443.normalize_pure_lets)
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
                  (fun uu____15473  ->
                     let uu____15474 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15475 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15474
                       uu____15475);
                (let uu____15476 =
                   let uu____15477 = FStar_Syntax_Subst.compress head2 in
                   uu____15477.FStar_Syntax_Syntax.n in
                 match uu____15476 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15495 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15495 with
                      | (uu____15496,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15502 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15510 =
                                   let uu____15511 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15511.FStar_Syntax_Syntax.n in
                                 match uu____15510 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15517,uu____15518))
                                     ->
                                     let uu____15527 =
                                       let uu____15528 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15528.FStar_Syntax_Syntax.n in
                                     (match uu____15527 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15534,msrc,uu____15536))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15545 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15545
                                      | uu____15546 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15547 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15548 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15548 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___138_15553 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___138_15553.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___138_15553.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___138_15553.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15554 = FStar_List.tl stack in
                                    let uu____15555 =
                                      let uu____15556 =
                                        let uu____15559 =
                                          let uu____15560 =
                                            let uu____15573 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15573) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15560 in
                                        FStar_Syntax_Syntax.mk uu____15559 in
                                      uu____15556
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15554 uu____15555
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15589 =
                                      let uu____15590 = is_return body in
                                      match uu____15590 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15594;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15595;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15600 -> false in
                                    if uu____15589
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
                                         let uu____15623 =
                                           let uu____15626 =
                                             let uu____15627 =
                                               let uu____15644 =
                                                 let uu____15647 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15647] in
                                               (uu____15644, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15627 in
                                           FStar_Syntax_Syntax.mk uu____15626 in
                                         uu____15623
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15663 =
                                           let uu____15664 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15664.FStar_Syntax_Syntax.n in
                                         match uu____15663 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15670::uu____15671::[])
                                             ->
                                             let uu____15678 =
                                               let uu____15681 =
                                                 let uu____15682 =
                                                   let uu____15689 =
                                                     let uu____15692 =
                                                       let uu____15693 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15693 in
                                                     let uu____15694 =
                                                       let uu____15697 =
                                                         let uu____15698 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15698 in
                                                       [uu____15697] in
                                                     uu____15692 ::
                                                       uu____15694 in
                                                   (bind1, uu____15689) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15682 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15681 in
                                             uu____15678
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15706 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15712 =
                                           let uu____15715 =
                                             let uu____15716 =
                                               let uu____15731 =
                                                 let uu____15734 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15735 =
                                                   let uu____15738 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15739 =
                                                     let uu____15742 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15743 =
                                                       let uu____15746 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15747 =
                                                         let uu____15750 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15751 =
                                                           let uu____15754 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15754] in
                                                         uu____15750 ::
                                                           uu____15751 in
                                                       uu____15746 ::
                                                         uu____15747 in
                                                     uu____15742 ::
                                                       uu____15743 in
                                                   uu____15738 :: uu____15739 in
                                                 uu____15734 :: uu____15735 in
                                               (bind_inst, uu____15731) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15716 in
                                           FStar_Syntax_Syntax.mk uu____15715 in
                                         uu____15712
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15766  ->
                                            let uu____15767 =
                                              FStar_Syntax_Print.term_to_string
                                                head0 in
                                            let uu____15768 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15767 uu____15768);
                                       (let uu____15769 = FStar_List.tl stack in
                                        norm cfg env uu____15769 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15793 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15793 with
                      | (uu____15794,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15829 =
                                  let uu____15830 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15830.FStar_Syntax_Syntax.n in
                                match uu____15829 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15836) -> t2
                                | uu____15841 -> head3 in
                              let uu____15842 =
                                let uu____15843 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15843.FStar_Syntax_Syntax.n in
                              match uu____15842 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15849 -> FStar_Pervasives_Native.None in
                            let uu____15850 = maybe_extract_fv head3 in
                            match uu____15850 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15860 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15860
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15865 = maybe_extract_fv head4 in
                                  match uu____15865 with
                                  | FStar_Pervasives_Native.Some uu____15870
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15871 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15876 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15891 =
                              match uu____15891 with
                              | (e,q) ->
                                  let uu____15898 =
                                    let uu____15899 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15899.FStar_Syntax_Syntax.n in
                                  (match uu____15898 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15914 -> false) in
                            let uu____15915 =
                              let uu____15916 =
                                let uu____15923 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15923 :: args in
                              FStar_Util.for_some is_arg_impure uu____15916 in
                            if uu____15915
                            then
                              let uu____15928 =
                                let uu____15929 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15929 in
                              failwith uu____15928
                            else ());
                           (let uu____15931 = maybe_unfold_action head_app in
                            match uu____15931 with
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
                                   (fun uu____15972  ->
                                      let uu____15973 =
                                        FStar_Syntax_Print.term_to_string
                                          head0 in
                                      let uu____15974 =
                                        FStar_Syntax_Print.term_to_string
                                          body1 in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15973 uu____15974);
                                 (let uu____15975 = FStar_List.tl stack in
                                  norm cfg env uu____15975 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15977) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16001 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____16001 in
                     (log cfg
                        (fun uu____16005  ->
                           let uu____16006 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16006);
                      (let uu____16007 = FStar_List.tl stack in
                       norm cfg env uu____16007 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____16009) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16134  ->
                               match uu____16134 with
                               | (pat,wopt,tm) ->
                                   let uu____16182 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____16182))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16214 = FStar_List.tl stack in
                     norm cfg env uu____16214 tm
                 | uu____16215 -> fallback ())
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
              (fun uu____16229  ->
                 let uu____16230 = FStar_Ident.string_of_lid msrc in
                 let uu____16231 = FStar_Ident.string_of_lid mtgt in
                 let uu____16232 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16230
                   uu____16231 uu____16232);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16234 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16234 with
               | (uu____16235,return_repr) ->
                   let return_inst =
                     let uu____16244 =
                       let uu____16245 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16245.FStar_Syntax_Syntax.n in
                     match uu____16244 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16251::[]) ->
                         let uu____16258 =
                           let uu____16261 =
                             let uu____16262 =
                               let uu____16269 =
                                 let uu____16272 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16272] in
                               (return_tm, uu____16269) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16262 in
                           FStar_Syntax_Syntax.mk uu____16261 in
                         uu____16258 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16280 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16283 =
                     let uu____16286 =
                       let uu____16287 =
                         let uu____16302 =
                           let uu____16305 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16306 =
                             let uu____16309 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16309] in
                           uu____16305 :: uu____16306 in
                         (return_inst, uu____16302) in
                       FStar_Syntax_Syntax.Tm_app uu____16287 in
                     FStar_Syntax_Syntax.mk uu____16286 in
                   uu____16283 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16318 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16318 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16321 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16321
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16322;
                     FStar_TypeChecker_Env.mtarget = uu____16323;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16324;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____16339 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16339
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16340;
                     FStar_TypeChecker_Env.mtarget = uu____16341;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16342;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16366 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16367 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16366 t FStar_Syntax_Syntax.tun uu____16367)
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
                (fun uu____16423  ->
                   match uu____16423 with
                   | (a,imp) ->
                       let uu____16434 = norm cfg env [] a in
                       (uu____16434, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___139_16448 = comp in
            let uu____16449 =
              let uu____16450 =
                let uu____16459 = norm cfg env [] t in
                let uu____16460 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16459, uu____16460) in
              FStar_Syntax_Syntax.Total uu____16450 in
            {
              FStar_Syntax_Syntax.n = uu____16449;
              FStar_Syntax_Syntax.pos =
                (uu___139_16448.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_16448.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___140_16475 = comp in
            let uu____16476 =
              let uu____16477 =
                let uu____16486 = norm cfg env [] t in
                let uu____16487 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16486, uu____16487) in
              FStar_Syntax_Syntax.GTotal uu____16477 in
            {
              FStar_Syntax_Syntax.n = uu____16476;
              FStar_Syntax_Syntax.pos =
                (uu___140_16475.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___140_16475.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16539  ->
                      match uu____16539 with
                      | (a,i) ->
                          let uu____16550 = norm cfg env [] a in
                          (uu____16550, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___87_16561  ->
                      match uu___87_16561 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16565 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16565
                      | f -> f)) in
            let uu___141_16569 = comp in
            let uu____16570 =
              let uu____16571 =
                let uu___142_16572 = ct in
                let uu____16573 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16574 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16577 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16573;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___142_16572.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16574;
                  FStar_Syntax_Syntax.effect_args = uu____16577;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16571 in
            {
              FStar_Syntax_Syntax.n = uu____16570;
              FStar_Syntax_Syntax.pos =
                (uu___141_16569.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___141_16569.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16588  ->
        match uu____16588 with
        | (x,imp) ->
            let uu____16591 =
              let uu___143_16592 = x in
              let uu____16593 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___143_16592.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___143_16592.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16593
              } in
            (uu____16591, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16599 =
          FStar_List.fold_left
            (fun uu____16617  ->
               fun b  ->
                 match uu____16617 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16599 with | (nbs,uu____16657) -> FStar_List.rev nbs
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
            let uu____16673 =
              let uu___144_16674 = rc in
              let uu____16675 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___144_16674.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16675;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___144_16674.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16673
        | uu____16682 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16695  ->
               let uu____16696 = FStar_Syntax_Print.tag_of_term t in
               let uu____16697 = FStar_Syntax_Print.term_to_string t in
               let uu____16698 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16705 =
                 let uu____16706 =
                   let uu____16709 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16709 in
                 stack_to_string uu____16706 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16696 uu____16697 uu____16698 uu____16705);
          (let t1 = maybe_simplify cfg env stack t in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16739 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16739
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16741 =
                     let uu____16742 =
                       let uu____16743 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16743 in
                     FStar_Util.string_of_int uu____16742 in
                   let uu____16748 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16749 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16741 uu____16748 uu____16749
                 else ());
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____16803  ->
                     let uu____16804 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16804);
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
               let uu____16840 =
                 let uu___145_16841 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___145_16841.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___145_16841.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16840
           | (Arg (Univ uu____16842,uu____16843,uu____16844))::uu____16845 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16848,uu____16849))::uu____16850 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____16866),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16919  ->
                     let uu____16920 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16920);
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
                  (let uu____16930 = FStar_ST.op_Bang m in
                   match uu____16930 with
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
                   | FStar_Pervasives_Native.Some (uu____17067,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1 in
               let fallback msg uu____17114 =
                 log cfg
                   (fun uu____17118  ->
                      let uu____17119 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____17119);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t2) in
               let uu____17123 =
                 let uu____17124 = FStar_Syntax_Subst.compress t1 in
                 uu____17124.FStar_Syntax_Syntax.n in
               (match uu____17123 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____17151 = closure_as_term cfg env1 ty in
                      reify_lift cfg t2 msrc mtgt uu____17151 in
                    (log cfg
                       (fun uu____17155  ->
                          let uu____17156 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____17156);
                     (let uu____17157 = FStar_List.tl stack in
                      norm cfg env1 uu____17157 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____17158);
                       FStar_Syntax_Syntax.pos = uu____17159;
                       FStar_Syntax_Syntax.vars = uu____17160;_},(e,uu____17162)::[])
                    -> norm cfg env1 stack' e
                | uu____17191 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17211  ->
                     let uu____17212 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17212);
                (let scrutinee = t1 in
                 let norm_and_rebuild_match uu____17217 =
                   log cfg
                     (fun uu____17222  ->
                        let uu____17223 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17224 =
                          let uu____17225 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17242  ->
                                    match uu____17242 with
                                    | (p,uu____17252,uu____17253) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17225
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17223 uu____17224);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___88_17270  ->
                                match uu___88_17270 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17271 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___146_17275 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___146_17275.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___146_17275.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___146_17275.memoize_lazy);
                        normalize_pure_lets =
                          (uu___146_17275.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17307 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17328 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17388  ->
                                    fun uu____17389  ->
                                      match (uu____17388, uu____17389) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17480 = norm_pat env3 p1 in
                                          (match uu____17480 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17328 with
                           | (pats1,env3) ->
                               ((let uu___147_17562 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___147_17562.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___148_17581 = x in
                            let uu____17582 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17581.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17581.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17582
                            } in
                          ((let uu___149_17596 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___149_17596.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___150_17607 = x in
                            let uu____17608 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___150_17607.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___150_17607.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17608
                            } in
                          ((let uu___151_17622 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___151_17622.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___152_17638 = x in
                            let uu____17639 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_17638.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_17638.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17639
                            } in
                          let t3 = norm_or_whnf env2 t2 in
                          ((let uu___153_17646 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___153_17646.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17656 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17670 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17670 with
                                  | (p,wopt,e) ->
                                      let uu____17690 = norm_pat env1 p in
                                      (match uu____17690 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17715 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17715 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17721 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17721) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17731) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17736 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17737;
                         FStar_Syntax_Syntax.fv_delta = uu____17738;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17739;
                         FStar_Syntax_Syntax.fv_delta = uu____17740;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17741);_}
                       -> true
                   | uu____17748 -> false in
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
                   let uu____17893 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17893 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17980 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18019 ->
                                 let uu____18020 =
                                   let uu____18021 = is_cons head1 in
                                   Prims.op_Negation uu____18021 in
                                 FStar_Util.Inr uu____18020)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18046 =
                              let uu____18047 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18047.FStar_Syntax_Syntax.n in
                            (match uu____18046 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18065 ->
                                 let uu____18066 =
                                   let uu____18067 = is_cons head1 in
                                   Prims.op_Negation uu____18067 in
                                 FStar_Util.Inr uu____18066))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____18136)::rest_a,(p1,uu____18139)::rest_p) ->
                       let uu____18183 = matches_pat t2 p1 in
                       (match uu____18183 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18232 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18338 = matches_pat scrutinee1 p1 in
                       (match uu____18338 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18378  ->
                                  let uu____18379 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18380 =
                                    let uu____18381 =
                                      FStar_List.map
                                        (fun uu____18391  ->
                                           match uu____18391 with
                                           | (uu____18396,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s in
                                    FStar_All.pipe_right uu____18381
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18379 uu____18380);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18427  ->
                                       match uu____18427 with
                                       | (bv,t2) ->
                                           let uu____18450 =
                                             let uu____18457 =
                                               let uu____18460 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18460 in
                                             let uu____18461 =
                                               let uu____18462 =
                                                 let uu____18493 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2)) in
                                                 ([], t2, uu____18493, false) in
                                               Clos uu____18462 in
                                             (uu____18457, uu____18461) in
                                           uu____18450 :: env2) env1 s in
                              let uu____18610 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18610))) in
                 let uu____18611 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18611
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___89_18632  ->
                match uu___89_18632 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18636 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18642 -> d in
      let uu____18645 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18647 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations) in
           Prims.op_Negation uu____18647) in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18645
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
            let uu___154_18672 = config s e in
            {
              steps = (uu___154_18672.steps);
              tcenv = (uu___154_18672.tcenv);
              delta_level = (uu___154_18672.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___154_18672.strong);
              memoize_lazy = (uu___154_18672.memoize_lazy);
              normalize_pure_lets = (uu___154_18672.normalize_pure_lets)
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
      fun t  -> let uu____18697 = config s e in norm_comp uu____18697 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18710 = config [] env in norm_universe uu____18710 [] u
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
        let uu____18728 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18728 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18735 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___155_18754 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___155_18754.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___155_18754.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18761 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18761
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
                  let uu___156_18770 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___156_18770.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___156_18770.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___156_18770.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___157_18772 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___157_18772.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___157_18772.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___157_18772.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___157_18772.FStar_Syntax_Syntax.flags)
                  } in
            let uu___158_18773 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___158_18773.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___158_18773.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18775 -> c
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
        let uu____18787 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18787 in
      let uu____18794 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18794
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18798  ->
                 let uu____18799 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18799)
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
            ((let uu____18816 =
                let uu____18821 =
                  let uu____18822 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18822 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18821) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18816);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18833 = config [AllowUnboundUniverses] env in
          norm_comp uu____18833 [] c
        with
        | e ->
            ((let uu____18846 =
                let uu____18851 =
                  let uu____18852 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18852 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18851) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18846);
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
                   let uu____18889 =
                     let uu____18890 =
                       let uu____18897 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18897) in
                     FStar_Syntax_Syntax.Tm_refine uu____18890 in
                   mk uu____18889 t01.FStar_Syntax_Syntax.pos
               | uu____18902 -> t2)
          | uu____18903 -> t2 in
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
        let uu____18943 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18943 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18972 ->
                 let uu____18979 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18979 with
                  | (actuals,uu____18989,uu____18990) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19004 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19004 with
                         | (binders,args) ->
                             let uu____19021 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19021
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
      | uu____19029 ->
          let uu____19030 = FStar_Syntax_Util.head_and_args t in
          (match uu____19030 with
           | (head1,args) ->
               let uu____19067 =
                 let uu____19068 = FStar_Syntax_Subst.compress head1 in
                 uu____19068.FStar_Syntax_Syntax.n in
               (match uu____19067 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19071,thead) ->
                    let uu____19097 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19097 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19139 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___163_19147 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___163_19147.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___163_19147.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___163_19147.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___163_19147.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___163_19147.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___163_19147.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___163_19147.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___163_19147.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___163_19147.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___163_19147.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___163_19147.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___163_19147.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___163_19147.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___163_19147.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___163_19147.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___163_19147.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___163_19147.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___163_19147.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___163_19147.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___163_19147.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___163_19147.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___163_19147.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___163_19147.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___163_19147.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___163_19147.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___163_19147.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___163_19147.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___163_19147.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___163_19147.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___163_19147.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___163_19147.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___163_19147.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19139 with
                            | (uu____19148,ty,uu____19150) ->
                                eta_expand_with_type env t ty))
                | uu____19151 ->
                    let uu____19152 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___164_19160 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___164_19160.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___164_19160.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___164_19160.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___164_19160.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___164_19160.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___164_19160.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___164_19160.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___164_19160.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___164_19160.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___164_19160.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___164_19160.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___164_19160.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___164_19160.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___164_19160.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___164_19160.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___164_19160.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___164_19160.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___164_19160.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___164_19160.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___164_19160.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___164_19160.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___164_19160.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___164_19160.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___164_19160.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___164_19160.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___164_19160.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___164_19160.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___164_19160.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___164_19160.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___164_19160.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___164_19160.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___164_19160.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19152 with
                     | (uu____19161,ty,uu____19163) ->
                         eta_expand_with_type env t ty)))
let rec elim_delayed_subst_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___165_19220 = x in
      let uu____19221 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___165_19220.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___165_19220.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____19221
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____19224 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____19249 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____19250 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____19251 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____19252 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____19259 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____19260 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___166_19288 = rc in
          let uu____19289 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____19296 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___166_19288.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____19289;
            FStar_Syntax_Syntax.residual_flags = uu____19296
          } in
        let uu____19299 =
          let uu____19300 =
            let uu____19317 = elim_delayed_subst_binders bs in
            let uu____19324 = elim_delayed_subst_term t2 in
            let uu____19325 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____19317, uu____19324, uu____19325) in
          FStar_Syntax_Syntax.Tm_abs uu____19300 in
        mk1 uu____19299
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____19354 =
          let uu____19355 =
            let uu____19368 = elim_delayed_subst_binders bs in
            let uu____19375 = elim_delayed_subst_comp c in
            (uu____19368, uu____19375) in
          FStar_Syntax_Syntax.Tm_arrow uu____19355 in
        mk1 uu____19354
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____19388 =
          let uu____19389 =
            let uu____19396 = elim_bv bv in
            let uu____19397 = elim_delayed_subst_term phi in
            (uu____19396, uu____19397) in
          FStar_Syntax_Syntax.Tm_refine uu____19389 in
        mk1 uu____19388
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____19420 =
          let uu____19421 =
            let uu____19436 = elim_delayed_subst_term t2 in
            let uu____19437 = elim_delayed_subst_args args in
            (uu____19436, uu____19437) in
          FStar_Syntax_Syntax.Tm_app uu____19421 in
        mk1 uu____19420
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___167_19501 = p in
              let uu____19502 =
                let uu____19503 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____19503 in
              {
                FStar_Syntax_Syntax.v = uu____19502;
                FStar_Syntax_Syntax.p =
                  (uu___167_19501.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___168_19505 = p in
              let uu____19506 =
                let uu____19507 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____19507 in
              {
                FStar_Syntax_Syntax.v = uu____19506;
                FStar_Syntax_Syntax.p =
                  (uu___168_19505.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___169_19514 = p in
              let uu____19515 =
                let uu____19516 =
                  let uu____19523 = elim_bv x in
                  let uu____19524 = elim_delayed_subst_term t0 in
                  (uu____19523, uu____19524) in
                FStar_Syntax_Syntax.Pat_dot_term uu____19516 in
              {
                FStar_Syntax_Syntax.v = uu____19515;
                FStar_Syntax_Syntax.p =
                  (uu___169_19514.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___170_19543 = p in
              let uu____19544 =
                let uu____19545 =
                  let uu____19558 =
                    FStar_List.map
                      (fun uu____19581  ->
                         match uu____19581 with
                         | (x,b) ->
                             let uu____19594 = elim_pat x in (uu____19594, b))
                      pats in
                  (fv, uu____19558) in
                FStar_Syntax_Syntax.Pat_cons uu____19545 in
              {
                FStar_Syntax_Syntax.v = uu____19544;
                FStar_Syntax_Syntax.p =
                  (uu___170_19543.FStar_Syntax_Syntax.p)
              }
          | uu____19607 -> p in
        let elim_branch uu____19629 =
          match uu____19629 with
          | (pat,wopt,t3) ->
              let uu____19655 = elim_pat pat in
              let uu____19658 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____19661 = elim_delayed_subst_term t3 in
              (uu____19655, uu____19658, uu____19661) in
        let uu____19666 =
          let uu____19667 =
            let uu____19690 = elim_delayed_subst_term t2 in
            let uu____19691 = FStar_List.map elim_branch branches in
            (uu____19690, uu____19691) in
          FStar_Syntax_Syntax.Tm_match uu____19667 in
        mk1 uu____19666
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____19800 =
          match uu____19800 with
          | (tc,topt) ->
              let uu____19835 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____19845 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____19845
                | FStar_Util.Inr c ->
                    let uu____19847 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____19847 in
              let uu____19848 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____19835, uu____19848) in
        let uu____19857 =
          let uu____19858 =
            let uu____19885 = elim_delayed_subst_term t2 in
            let uu____19886 = elim_ascription a in
            (uu____19885, uu____19886, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____19858 in
        mk1 uu____19857
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___171_19931 = lb in
          let uu____19932 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____19935 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___171_19931.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___171_19931.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____19932;
            FStar_Syntax_Syntax.lbeff =
              (uu___171_19931.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____19935
          } in
        let uu____19938 =
          let uu____19939 =
            let uu____19952 =
              let uu____19959 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____19959) in
            let uu____19968 = elim_delayed_subst_term t2 in
            (uu____19952, uu____19968) in
          FStar_Syntax_Syntax.Tm_let uu____19939 in
        mk1 uu____19938
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____20001 =
          let uu____20002 =
            let uu____20019 = elim_delayed_subst_term t2 in (uv, uu____20019) in
          FStar_Syntax_Syntax.Tm_uvar uu____20002 in
        mk1 uu____20001
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____20036 =
          let uu____20037 =
            let uu____20044 = elim_delayed_subst_term t2 in
            let uu____20045 = elim_delayed_subst_meta md in
            (uu____20044, uu____20045) in
          FStar_Syntax_Syntax.Tm_meta uu____20037 in
        mk1 uu____20036
and elim_delayed_subst_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___90_20052  ->
         match uu___90_20052 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____20056 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____20056
         | f -> f) flags1
and elim_delayed_subst_comp:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____20077 =
          let uu____20078 =
            let uu____20087 = elim_delayed_subst_term t in
            (uu____20087, uopt) in
          FStar_Syntax_Syntax.Total uu____20078 in
        mk1 uu____20077
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____20100 =
          let uu____20101 =
            let uu____20110 = elim_delayed_subst_term t in
            (uu____20110, uopt) in
          FStar_Syntax_Syntax.GTotal uu____20101 in
        mk1 uu____20100
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___172_20115 = ct in
          let uu____20116 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____20119 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____20128 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___172_20115.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___172_20115.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____20116;
            FStar_Syntax_Syntax.effect_args = uu____20119;
            FStar_Syntax_Syntax.flags = uu____20128
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and elim_delayed_subst_meta:
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata =
  fun uu___91_20131  ->
    match uu___91_20131 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____20143 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____20143
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____20176 =
          let uu____20183 = elim_delayed_subst_term t in (m, uu____20183) in
        FStar_Syntax_Syntax.Meta_monadic uu____20176
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____20191 =
          let uu____20200 = elim_delayed_subst_term t in
          (m1, m2, uu____20200) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____20191
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____20208 =
          let uu____20217 = elim_delayed_subst_term t in (d, s, uu____20217) in
        FStar_Syntax_Syntax.Meta_alien uu____20208
    | m -> m
and elim_delayed_subst_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.map
      (fun uu____20240  ->
         match uu____20240 with
         | (t,q) ->
             let uu____20251 = elim_delayed_subst_term t in (uu____20251, q))
      args
and elim_delayed_subst_binders:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    FStar_List.map
      (fun uu____20271  ->
         match uu____20271 with
         | (x,q) ->
             let uu____20282 =
               let uu___173_20283 = x in
               let uu____20284 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___173_20283.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___173_20283.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____20284
               } in
             (uu____20282, q)) bs
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
            | (uu____20360,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____20366,FStar_Util.Inl t) ->
                let uu____20372 =
                  let uu____20375 =
                    let uu____20376 =
                      let uu____20389 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____20389) in
                    FStar_Syntax_Syntax.Tm_arrow uu____20376 in
                  FStar_Syntax_Syntax.mk uu____20375 in
                uu____20372 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____20393 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____20393 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____20421 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____20476 ->
                    let uu____20477 =
                      let uu____20486 =
                        let uu____20487 = FStar_Syntax_Subst.compress t4 in
                        uu____20487.FStar_Syntax_Syntax.n in
                      (uu____20486, tc) in
                    (match uu____20477 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____20512) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____20549) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____20588,FStar_Util.Inl uu____20589) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____20612 -> failwith "Impossible") in
              (match uu____20421 with
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
          let uu____20717 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____20717 with
          | (univ_names1,binders1,tc) ->
              let uu____20775 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20775)
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
          let uu____20810 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20810 with
          | (univ_names1,binders1,tc) ->
              let uu____20870 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20870)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20903 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20903 with
           | (univ_names1,binders1,typ1) ->
               let uu___174_20931 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20931.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20931.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20931.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20931.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___175_20952 = s in
          let uu____20953 =
            let uu____20954 =
              let uu____20963 = FStar_List.map (elim_uvars env) sigs in
              (uu____20963, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20954 in
          {
            FStar_Syntax_Syntax.sigel = uu____20953;
            FStar_Syntax_Syntax.sigrng =
              (uu___175_20952.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___175_20952.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___175_20952.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___175_20952.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20980 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20980 with
           | (univ_names1,uu____20998,typ1) ->
               let uu___176_21012 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___176_21012.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___176_21012.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___176_21012.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___176_21012.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____21018 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____21018 with
           | (univ_names1,uu____21036,typ1) ->
               let uu___177_21050 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___177_21050.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___177_21050.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___177_21050.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___177_21050.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____21084 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____21084 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____21107 =
                            let uu____21108 =
                              let uu____21109 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____21109 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____21108 in
                          elim_delayed_subst_term uu____21107 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___178_21112 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___178_21112.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___178_21112.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___179_21113 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___179_21113.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___179_21113.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___179_21113.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___179_21113.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___180_21125 = s in
          let uu____21126 =
            let uu____21127 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____21127 in
          {
            FStar_Syntax_Syntax.sigel = uu____21126;
            FStar_Syntax_Syntax.sigrng =
              (uu___180_21125.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___180_21125.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___180_21125.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___180_21125.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____21131 = elim_uvars_aux_t env us [] t in
          (match uu____21131 with
           | (us1,uu____21149,t1) ->
               let uu___181_21163 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___181_21163.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___181_21163.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___181_21163.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___181_21163.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21164 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21166 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____21166 with
           | (univs1,binders,signature) ->
               let uu____21194 =
                 let uu____21203 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____21203 with
                 | (univs_opening,univs2) ->
                     let uu____21230 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____21230) in
               (match uu____21194 with
                | (univs_opening,univs_closing) ->
                    let uu____21247 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____21253 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____21254 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____21253, uu____21254) in
                    (match uu____21247 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____21276 =
                           match uu____21276 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____21294 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____21294 with
                                | (us1,t1) ->
                                    let uu____21305 =
                                      let uu____21310 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____21317 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____21310, uu____21317) in
                                    (match uu____21305 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____21330 =
                                           let uu____21335 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____21344 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____21335, uu____21344) in
                                         (match uu____21330 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____21360 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____21360 in
                                              let uu____21361 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____21361 with
                                               | (uu____21382,uu____21383,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____21398 =
                                                       let uu____21399 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____21399 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____21398 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____21404 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____21404 with
                           | (uu____21417,uu____21418,t1) -> t1 in
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
                             | uu____21478 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____21495 =
                               let uu____21496 =
                                 FStar_Syntax_Subst.compress body in
                               uu____21496.FStar_Syntax_Syntax.n in
                             match uu____21495 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____21555 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____21584 =
                               let uu____21585 =
                                 FStar_Syntax_Subst.compress t in
                               uu____21585.FStar_Syntax_Syntax.n in
                             match uu____21584 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____21606) ->
                                 let uu____21627 = destruct_action_body body in
                                 (match uu____21627 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____21672 ->
                                 let uu____21673 = destruct_action_body t in
                                 (match uu____21673 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____21722 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____21722 with
                           | (action_univs,t) ->
                               let uu____21731 = destruct_action_typ_templ t in
                               (match uu____21731 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___182_21772 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___182_21772.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___182_21772.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___183_21774 = ed in
                           let uu____21775 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21776 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21777 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21778 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21779 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21780 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21781 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21782 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21783 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21784 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21785 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21786 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21787 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21788 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___183_21774.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___183_21774.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21775;
                             FStar_Syntax_Syntax.bind_wp = uu____21776;
                             FStar_Syntax_Syntax.if_then_else = uu____21777;
                             FStar_Syntax_Syntax.ite_wp = uu____21778;
                             FStar_Syntax_Syntax.stronger = uu____21779;
                             FStar_Syntax_Syntax.close_wp = uu____21780;
                             FStar_Syntax_Syntax.assert_p = uu____21781;
                             FStar_Syntax_Syntax.assume_p = uu____21782;
                             FStar_Syntax_Syntax.null_wp = uu____21783;
                             FStar_Syntax_Syntax.trivial = uu____21784;
                             FStar_Syntax_Syntax.repr = uu____21785;
                             FStar_Syntax_Syntax.return_repr = uu____21786;
                             FStar_Syntax_Syntax.bind_repr = uu____21787;
                             FStar_Syntax_Syntax.actions = uu____21788
                           } in
                         let uu___184_21791 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___184_21791.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___184_21791.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___184_21791.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___184_21791.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___92_21808 =
            match uu___92_21808 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21835 = elim_uvars_aux_t env us [] t in
                (match uu____21835 with
                 | (us1,uu____21859,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___185_21878 = sub_eff in
            let uu____21879 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21882 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___185_21878.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___185_21878.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21879;
              FStar_Syntax_Syntax.lift = uu____21882
            } in
          let uu___186_21885 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___186_21885.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___186_21885.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___186_21885.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___186_21885.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____21895 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21895 with
           | (univ_names1,binders1,comp1) ->
               let uu___187_21929 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___187_21929.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___187_21929.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___187_21929.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___187_21929.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21940 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t