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
  | Unmeta[@@deriving show]
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____184  -> []) }
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
    match projectee with | Clos _0 -> true | uu____385 -> false
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
    match projectee with | Univ _0 -> true | uu____487 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____498 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___74_517  ->
    match uu___74_517 with
    | Clos (uu____518,t,uu____520,uu____521) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____566 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____846 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____882 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____918 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____987 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1029 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1085 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1125 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1157 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1193 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1209 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1234 .
    'Auu____1234 ->
      FStar_Range.range -> 'Auu____1234 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1288 = FStar_ST.op_Bang r in
          match uu____1288 with
          | FStar_Pervasives_Native.Some uu____1336 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1390 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1390 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___75_1397  ->
    match uu___75_1397 with
    | Arg (c,uu____1399,uu____1400) ->
        let uu____1401 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1401
    | MemoLazy uu____1402 -> "MemoLazy"
    | Abs (uu____1409,bs,uu____1411,uu____1412,uu____1413) ->
        let uu____1418 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1418
    | UnivArgs uu____1423 -> "UnivArgs"
    | Match uu____1430 -> "Match"
    | App (uu____1437,t,uu____1439,uu____1440) ->
        let uu____1441 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1441
    | Meta (m,uu____1443) -> "Meta"
    | Let uu____1444 -> "Let"
    | Cfg uu____1453 -> "Cfg"
    | Debug (t,uu____1455) ->
        let uu____1456 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1456
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1464 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1464 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1480 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1480 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1493 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1493 then f () else ()
let is_empty: 'Auu____1497 . 'Auu____1497 Prims.list -> Prims.bool =
  fun uu___76_1503  ->
    match uu___76_1503 with | [] -> true | uu____1506 -> false
let lookup_bvar:
  'Auu____1513 'Auu____1514 .
    ('Auu____1514,'Auu____1513) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1513
  =
  fun env  ->
    fun x  ->
      try
        let uu____1538 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1538
      with
      | uu____1551 ->
          let uu____1552 =
            let uu____1553 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1553 in
          failwith uu____1552
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
          let uu____1590 =
            FStar_List.fold_left
              (fun uu____1616  ->
                 fun u1  ->
                   match uu____1616 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1641 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1641 with
                        | (k_u,n1) ->
                            let uu____1656 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1656
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1590 with
          | (uu____1674,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1699 =
                   let uu____1700 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1700 in
                 match uu____1699 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1718 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1727 ->
                   let uu____1728 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1728
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1734 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1743 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1752 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1759 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1759 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1776 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1776 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1784 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1792 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1792 with
                                  | (uu____1797,m) -> n1 <= m)) in
                        if uu____1784 then rest1 else us1
                    | uu____1802 -> us1)
               | uu____1807 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1811 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1811 in
        let uu____1814 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1814
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1816 = aux u in
           match uu____1816 with
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
          (fun uu____1920  ->
             let uu____1921 = FStar_Syntax_Print.tag_of_term t in
             let uu____1922 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1921
               uu____1922);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1929 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1931 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1956 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1957 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1958 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1959 ->
                  let uu____1976 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1976
                  then
                    let uu____1977 =
                      let uu____1978 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1979 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1978 uu____1979 in
                    failwith uu____1977
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1982 =
                    let uu____1983 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1983 in
                  mk uu____1982 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1990 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1990
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1992 = lookup_bvar env x in
                  (match uu____1992 with
                   | Univ uu____1995 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1998,uu____1999) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2111 = closures_as_binders_delayed cfg env bs in
                  (match uu____2111 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2139 =
                         let uu____2140 =
                           let uu____2157 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2157) in
                         FStar_Syntax_Syntax.Tm_abs uu____2140 in
                       mk uu____2139 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2188 = closures_as_binders_delayed cfg env bs in
                  (match uu____2188 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2230 =
                    let uu____2241 =
                      let uu____2248 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2248] in
                    closures_as_binders_delayed cfg env uu____2241 in
                  (match uu____2230 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2266 =
                         let uu____2267 =
                           let uu____2274 =
                             let uu____2275 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2275
                               FStar_Pervasives_Native.fst in
                           (uu____2274, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2267 in
                       mk uu____2266 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2366 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2366
                    | FStar_Util.Inr c ->
                        let uu____2380 = close_comp cfg env c in
                        FStar_Util.Inr uu____2380 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2396 =
                    let uu____2397 =
                      let uu____2424 = closure_as_term_delayed cfg env t11 in
                      (uu____2424, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2397 in
                  mk uu____2396 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2475 =
                    let uu____2476 =
                      let uu____2483 = closure_as_term_delayed cfg env t' in
                      let uu____2486 =
                        let uu____2487 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2487 in
                      (uu____2483, uu____2486) in
                    FStar_Syntax_Syntax.Tm_meta uu____2476 in
                  mk uu____2475 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2547 =
                    let uu____2548 =
                      let uu____2555 = closure_as_term_delayed cfg env t' in
                      let uu____2558 =
                        let uu____2559 =
                          let uu____2566 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2566) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2559 in
                      (uu____2555, uu____2558) in
                    FStar_Syntax_Syntax.Tm_meta uu____2548 in
                  mk uu____2547 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2585 =
                    let uu____2586 =
                      let uu____2593 = closure_as_term_delayed cfg env t' in
                      let uu____2596 =
                        let uu____2597 =
                          let uu____2606 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2606) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2597 in
                      (uu____2593, uu____2596) in
                    FStar_Syntax_Syntax.Tm_meta uu____2586 in
                  mk uu____2585 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2619 =
                    let uu____2620 =
                      let uu____2627 = closure_as_term_delayed cfg env t' in
                      (uu____2627, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2620 in
                  mk uu____2619 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2667  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2686 =
                    let uu____2697 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2697
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2716 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___97_2728 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___97_2728.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___97_2728.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2716)) in
                  (match uu____2686 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___98_2744 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___98_2744.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___98_2744.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2755,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2814  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2839 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2839
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2859  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2881 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2881
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___99_2893 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___99_2893.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___99_2893.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___100_2894 = lb in
                    let uu____2895 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___100_2894.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___100_2894.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2895
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2925  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3014 =
                    match uu____3014 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3069 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3090 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3150  ->
                                        fun uu____3151  ->
                                          match (uu____3150, uu____3151) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3242 =
                                                norm_pat env3 p1 in
                                              (match uu____3242 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3090 with
                               | (pats1,env3) ->
                                   ((let uu___101_3324 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___101_3324.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___102_3343 = x in
                                let uu____3344 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3343.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3343.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3344
                                } in
                              ((let uu___103_3358 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3358.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___104_3369 = x in
                                let uu____3370 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___104_3369.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___104_3369.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3370
                                } in
                              ((let uu___105_3384 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___105_3384.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___106_3400 = x in
                                let uu____3401 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___106_3400.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___106_3400.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3401
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___107_3408 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___107_3408.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3411 = norm_pat env1 pat in
                        (match uu____3411 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3440 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3440 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3446 =
                    let uu____3447 =
                      let uu____3470 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3470) in
                    FStar_Syntax_Syntax.Tm_match uu____3447 in
                  mk uu____3446 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3556 -> closure_as_term cfg env t
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
        | uu____3582 ->
            FStar_List.map
              (fun uu____3599  ->
                 match uu____3599 with
                 | (x,imp) ->
                     let uu____3618 = closure_as_term_delayed cfg env x in
                     (uu____3618, imp)) args
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
        let uu____3632 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3681  ->
                  fun uu____3682  ->
                    match (uu____3681, uu____3682) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___108_3752 = b in
                          let uu____3753 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___108_3752.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___108_3752.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3753
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3632 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3846 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3859 = closure_as_term_delayed cfg env t in
                 let uu____3860 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3859 uu____3860
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3873 = closure_as_term_delayed cfg env t in
                 let uu____3874 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3873 uu____3874
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
                        (fun uu___77_3900  ->
                           match uu___77_3900 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3904 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3904
                           | f -> f)) in
                 let uu____3908 =
                   let uu___109_3909 = c1 in
                   let uu____3910 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3910;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___109_3909.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3908)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___78_3920  ->
            match uu___78_3920 with
            | FStar_Syntax_Syntax.DECREASES uu____3921 -> false
            | uu____3924 -> true))
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
                   (fun uu___79_3942  ->
                      match uu___79_3942 with
                      | FStar_Syntax_Syntax.DECREASES uu____3943 -> false
                      | uu____3946 -> true)) in
            let rc1 =
              let uu___110_3948 = rc in
              let uu____3949 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___110_3948.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3949;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3956 -> lopt
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
    let uu____4041 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4041 in
  let arg_as_bounded_int uu____4069 =
    match uu____4069 with
    | (a,uu____4081) ->
        let uu____4088 =
          let uu____4089 = FStar_Syntax_Subst.compress a in
          uu____4089.FStar_Syntax_Syntax.n in
        (match uu____4088 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4099;
                FStar_Syntax_Syntax.vars = uu____4100;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4102;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4103;_},uu____4104)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4143 =
               let uu____4148 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4148) in
             FStar_Pervasives_Native.Some uu____4143
         | uu____4153 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4193 = f a in FStar_Pervasives_Native.Some uu____4193
    | uu____4194 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4242 = f a0 a1 in FStar_Pervasives_Native.Some uu____4242
    | uu____4243 -> FStar_Pervasives_Native.None in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4285 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____4285)) a416 a417 a418 a419 a420 in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4334 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____4334)) a423 a424 a425 a426 a427 in
  let as_primitive_step uu____4358 =
    match uu____4358 with
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
                   let uu____4406 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4406)) a429 a430) in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4434 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4434)) a432
               a433 a434) in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4455 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4455)) a436
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
                       let uu____4483 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4483)) a439
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
                       let uu____4511 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4511))
               a443 a444 a445) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4619 =
          let uu____4628 = as_a a in
          let uu____4631 = as_b b in (uu____4628, uu____4631) in
        (match uu____4619 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4646 =
               let uu____4647 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4647 in
             FStar_Pervasives_Native.Some uu____4646
         | uu____4648 -> FStar_Pervasives_Native.None)
    | uu____4657 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4671 =
        let uu____4672 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4672 in
      mk uu____4671 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4682 =
      let uu____4685 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4685 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4682 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4717 =
      let uu____4718 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4718 in
    FStar_Syntax_Embeddings.embed_int rng uu____4717 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4736 = arg_as_string a1 in
        (match uu____4736 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4742 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4742 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4755 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4755
              | uu____4756 -> FStar_Pervasives_Native.None)
         | uu____4761 -> FStar_Pervasives_Native.None)
    | uu____4764 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4774 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4774 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4798 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4809 =
          let uu____4830 = arg_as_string fn in
          let uu____4833 = arg_as_int from_line in
          let uu____4836 = arg_as_int from_col in
          let uu____4839 = arg_as_int to_line in
          let uu____4842 = arg_as_int to_col in
          (uu____4830, uu____4833, uu____4836, uu____4839, uu____4842) in
        (match uu____4809 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4873 =
                 let uu____4874 = FStar_BigInt.to_int_fs from_l in
                 let uu____4875 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4874 uu____4875 in
               let uu____4876 =
                 let uu____4877 = FStar_BigInt.to_int_fs to_l in
                 let uu____4878 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4877 uu____4878 in
               FStar_Range.mk_range fn1 uu____4873 uu____4876 in
             let uu____4879 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4879
         | uu____4884 -> FStar_Pervasives_Native.None)
    | uu____4905 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4932)::(a1,uu____4934)::(a2,uu____4936)::[] ->
        let uu____4973 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4973 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4986 -> FStar_Pervasives_Native.None)
    | uu____4987 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5014)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5023 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5047 =
      let uu____5062 =
        let uu____5077 =
          let uu____5092 =
            let uu____5107 =
              let uu____5122 =
                let uu____5137 =
                  let uu____5152 =
                    let uu____5167 =
                      let uu____5182 =
                        let uu____5197 =
                          let uu____5212 =
                            let uu____5227 =
                              let uu____5242 =
                                let uu____5257 =
                                  let uu____5272 =
                                    let uu____5287 =
                                      let uu____5302 =
                                        let uu____5317 =
                                          let uu____5332 =
                                            let uu____5347 =
                                              let uu____5362 =
                                                let uu____5375 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5375,
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
                                              let uu____5382 =
                                                let uu____5397 =
                                                  let uu____5410 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5410,
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
                                                let uu____5417 =
                                                  let uu____5432 =
                                                    let uu____5447 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5447,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5456 =
                                                    let uu____5473 =
                                                      let uu____5488 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5488,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5497 =
                                                      let uu____5514 =
                                                        let uu____5533 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5533,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5514] in
                                                    uu____5473 :: uu____5497 in
                                                  uu____5432 :: uu____5456 in
                                                uu____5397 :: uu____5417 in
                                              uu____5362 :: uu____5382 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5347 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5332 in
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
                                          :: uu____5317 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____5302 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____5287 in
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
                                                        let uu____5750 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5750 y)) a466
                                                a467 a468)))
                                    :: uu____5272 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5257 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5242 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5227 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5212 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5197 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5182 in
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
                                          let uu____5917 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5917)) a470 a471 a472)))
                      :: uu____5167 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5943 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5943)) a474 a475 a476)))
                    :: uu____5152 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5969 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5969)) a478 a479 a480)))
                  :: uu____5137 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5995 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5995)) a482 a483 a484)))
                :: uu____5122 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5107 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5092 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5077 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5062 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5047 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6148 =
        let uu____6149 =
          let uu____6150 = FStar_Syntax_Syntax.as_arg c in [uu____6150] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6149 in
      uu____6148 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6200 =
                let uu____6213 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6213, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6229  ->
                                    fun uu____6230  ->
                                      match (uu____6229, uu____6230) with
                                      | ((int_to_t1,x),(uu____6249,y)) ->
                                          let uu____6259 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6259)) a486 a487 a488))) in
              let uu____6260 =
                let uu____6275 =
                  let uu____6288 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6288, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6304  ->
                                      fun uu____6305  ->
                                        match (uu____6304, uu____6305) with
                                        | ((int_to_t1,x),(uu____6324,y)) ->
                                            let uu____6334 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6334)) a490 a491 a492))) in
                let uu____6335 =
                  let uu____6350 =
                    let uu____6363 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6363, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6379  ->
                                        fun uu____6380  ->
                                          match (uu____6379, uu____6380) with
                                          | ((int_to_t1,x),(uu____6399,y)) ->
                                              let uu____6409 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____6409)) a494 a495 a496))) in
                  let uu____6410 =
                    let uu____6425 =
                      let uu____6438 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____6438, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6450  ->
                                        match uu____6450 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499))) in
                    [uu____6425] in
                  uu____6350 :: uu____6410 in
                uu____6275 :: uu____6335 in
              uu____6200 :: uu____6260)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6564 =
                let uu____6577 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6577, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6593  ->
                                    fun uu____6594  ->
                                      match (uu____6593, uu____6594) with
                                      | ((int_to_t1,x),(uu____6613,y)) ->
                                          let uu____6623 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6623)) a501 a502 a503))) in
              let uu____6624 =
                let uu____6639 =
                  let uu____6652 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6652, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6668  ->
                                      fun uu____6669  ->
                                        match (uu____6668, uu____6669) with
                                        | ((int_to_t1,x),(uu____6688,y)) ->
                                            let uu____6698 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6698)) a505 a506 a507))) in
                [uu____6639] in
              uu____6564 :: uu____6624)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6788)::(a1,uu____6790)::(a2,uu____6792)::[] ->
        let uu____6829 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6829 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_6835 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_6835.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_6835.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6839 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6839.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6839.FStar_Syntax_Syntax.vars)
                })
         | uu____6840 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6842)::uu____6843::(a1,uu____6845)::(a2,uu____6847)::[] ->
        let uu____6896 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6896 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_6902 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_6902.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_6902.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6906 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6906.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6906.FStar_Syntax_Syntax.vars)
                })
         | uu____6907 -> FStar_Pervasives_Native.None)
    | uu____6908 -> failwith "Unexpected number of arguments" in
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
      let uu____6927 =
        let uu____6928 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6928 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6927
    with | uu____6934 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6938 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6938) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6998  ->
           fun subst1  ->
             match uu____6998 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____7039,uu____7040)) ->
                      let uu____7099 = b in
                      (match uu____7099 with
                       | (bv,uu____7107) ->
                           let uu____7108 =
                             let uu____7109 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7109 in
                           if uu____7108
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7114 = unembed_binder term1 in
                              match uu____7114 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7121 =
                                      let uu___115_7122 = bv in
                                      let uu____7123 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___115_7122.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___115_7122.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7123
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7121 in
                                  let b_for_x =
                                    let uu____7127 =
                                      let uu____7134 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7134) in
                                    FStar_Syntax_Syntax.NT uu____7127 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___80_7143  ->
                                         match uu___80_7143 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7144,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7146;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7147;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7152 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7153 -> subst1)) env []
let reduce_primops:
  'Auu____7170 'Auu____7171 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7171) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7170 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7212 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7212
          then tm
          else
            (let uu____7214 = FStar_Syntax_Util.head_and_args tm in
             match uu____7214 with
             | (head1,args) ->
                 let uu____7251 =
                   let uu____7252 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7252.FStar_Syntax_Syntax.n in
                 (match uu____7251 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7256 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7256 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7273  ->
                                   let uu____7274 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7275 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7282 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7274 uu____7275 uu____7282);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7287  ->
                                   let uu____7288 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7288);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7291  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7293 =
                                 prim_step.interpretation psc args in
                               match uu____7293 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7299  ->
                                         let uu____7300 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7300);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7306  ->
                                         let uu____7307 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7308 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7307 uu____7308);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7309 ->
                           (log_primops cfg
                              (fun uu____7313  ->
                                 let uu____7314 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7314);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7318  ->
                            let uu____7319 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7319);
                       (match args with
                        | (a1,uu____7321)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7338 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7350  ->
                            let uu____7351 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7351);
                       (match args with
                        | (t,uu____7353)::(r,uu____7355)::[] ->
                            let uu____7382 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7382 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___116_7386 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___116_7386.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___116_7386.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7389 -> tm))
                  | uu____7398 -> tm))
let reduce_equality:
  'Auu____7403 'Auu____7404 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7404) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7403 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___117_7442 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___117_7442.tcenv);
           delta_level = (uu___117_7442.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___117_7442.strong);
           memoize_lazy = (uu___117_7442.memoize_lazy);
           normalize_pure_lets = (uu___117_7442.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____7449 'Auu____7450 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7450) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7449 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7492 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7492
          then tm1
          else
            (let w t =
               let uu___118_7504 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___118_7504.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___118_7504.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7521 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7526 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7526
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7547 =
                 match uu____7547 with
                 | (t1,q) ->
                     let uu____7560 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7560 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7588 -> (t1, q)) in
               let uu____7597 = FStar_Syntax_Util.head_and_args t in
               match uu____7597 with
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
                         FStar_Syntax_Syntax.pos = uu____7694;
                         FStar_Syntax_Syntax.vars = uu____7695;_},uu____7696);
                    FStar_Syntax_Syntax.pos = uu____7697;
                    FStar_Syntax_Syntax.vars = uu____7698;_},args)
                 ->
                 let uu____7724 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7724
                 then
                   let uu____7725 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7725 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7780)::
                        (uu____7781,(arg,uu____7783))::[] ->
                        maybe_auto_squash arg
                    | (uu____7848,(arg,uu____7850))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7851)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7916)::uu____7917::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7980::(FStar_Pervasives_Native.Some (false
                                   ),uu____7981)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8044 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8060 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8060
                    then
                      let uu____8061 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8061 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8116)::uu____8117::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8180::(FStar_Pervasives_Native.Some (true
                                     ),uu____8181)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8244)::
                          (uu____8245,(arg,uu____8247))::[] ->
                          maybe_auto_squash arg
                      | (uu____8312,(arg,uu____8314))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8315)::[]
                          -> maybe_auto_squash arg
                      | uu____8380 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8396 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8396
                       then
                         let uu____8397 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8397 with
                         | uu____8452::(FStar_Pervasives_Native.Some (true
                                        ),uu____8453)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8516)::uu____8517::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8580)::
                             (uu____8581,(arg,uu____8583))::[] ->
                             maybe_auto_squash arg
                         | (uu____8648,(p,uu____8650))::(uu____8651,(q,uu____8653))::[]
                             ->
                             let uu____8718 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8718
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8720 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8736 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8736
                          then
                            let uu____8737 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8737 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8792)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8831)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8870 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8886 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8886
                             then
                               match args with
                               | (t,uu____8888)::[] ->
                                   let uu____8905 =
                                     let uu____8906 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8906.FStar_Syntax_Syntax.n in
                                   (match uu____8905 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8909::[],body,uu____8911) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8938 -> tm1)
                                    | uu____8941 -> tm1)
                               | (uu____8942,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8943))::
                                   (t,uu____8945)::[] ->
                                   let uu____8984 =
                                     let uu____8985 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8985.FStar_Syntax_Syntax.n in
                                   (match uu____8984 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8988::[],body,uu____8990) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9017 -> tm1)
                                    | uu____9020 -> tm1)
                               | uu____9021 -> tm1
                             else
                               (let uu____9031 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9031
                                then
                                  match args with
                                  | (t,uu____9033)::[] ->
                                      let uu____9050 =
                                        let uu____9051 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9051.FStar_Syntax_Syntax.n in
                                      (match uu____9050 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9054::[],body,uu____9056)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9083 -> tm1)
                                       | uu____9086 -> tm1)
                                  | (uu____9087,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9088))::(t,uu____9090)::[] ->
                                      let uu____9129 =
                                        let uu____9130 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9130.FStar_Syntax_Syntax.n in
                                      (match uu____9129 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9133::[],body,uu____9135)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9162 -> tm1)
                                       | uu____9165 -> tm1)
                                  | uu____9166 -> tm1
                                else
                                  (let uu____9176 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9176
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9177;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9178;_},uu____9179)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9196;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9197;_},uu____9198)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9215 -> tm1
                                   else
                                     (let uu____9225 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9225 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9245 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9255;
                    FStar_Syntax_Syntax.vars = uu____9256;_},args)
                 ->
                 let uu____9278 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9278
                 then
                   let uu____9279 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9279 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9334)::
                        (uu____9335,(arg,uu____9337))::[] ->
                        maybe_auto_squash arg
                    | (uu____9402,(arg,uu____9404))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9405)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9470)::uu____9471::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9534::(FStar_Pervasives_Native.Some (false
                                   ),uu____9535)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9598 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9614 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9614
                    then
                      let uu____9615 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9615 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9670)::uu____9671::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9734::(FStar_Pervasives_Native.Some (true
                                     ),uu____9735)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9798)::
                          (uu____9799,(arg,uu____9801))::[] ->
                          maybe_auto_squash arg
                      | (uu____9866,(arg,uu____9868))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9869)::[]
                          -> maybe_auto_squash arg
                      | uu____9934 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9950 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9950
                       then
                         let uu____9951 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9951 with
                         | uu____10006::(FStar_Pervasives_Native.Some (true
                                         ),uu____10007)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10070)::uu____10071::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10134)::
                             (uu____10135,(arg,uu____10137))::[] ->
                             maybe_auto_squash arg
                         | (uu____10202,(p,uu____10204))::(uu____10205,
                                                           (q,uu____10207))::[]
                             ->
                             let uu____10272 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10272
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10274 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10290 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10290
                          then
                            let uu____10291 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10291 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10346)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10385)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10424 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10440 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10440
                             then
                               match args with
                               | (t,uu____10442)::[] ->
                                   let uu____10459 =
                                     let uu____10460 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10460.FStar_Syntax_Syntax.n in
                                   (match uu____10459 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10463::[],body,uu____10465) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10492 -> tm1)
                                    | uu____10495 -> tm1)
                               | (uu____10496,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10497))::
                                   (t,uu____10499)::[] ->
                                   let uu____10538 =
                                     let uu____10539 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10539.FStar_Syntax_Syntax.n in
                                   (match uu____10538 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10542::[],body,uu____10544) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10571 -> tm1)
                                    | uu____10574 -> tm1)
                               | uu____10575 -> tm1
                             else
                               (let uu____10585 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10585
                                then
                                  match args with
                                  | (t,uu____10587)::[] ->
                                      let uu____10604 =
                                        let uu____10605 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10605.FStar_Syntax_Syntax.n in
                                      (match uu____10604 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10608::[],body,uu____10610)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10637 -> tm1)
                                       | uu____10640 -> tm1)
                                  | (uu____10641,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10642))::(t,uu____10644)::[] ->
                                      let uu____10683 =
                                        let uu____10684 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10684.FStar_Syntax_Syntax.n in
                                      (match uu____10683 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10687::[],body,uu____10689)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10716 -> tm1)
                                       | uu____10719 -> tm1)
                                  | uu____10720 -> tm1
                                else
                                  (let uu____10730 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10730
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10731;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10732;_},uu____10733)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10750;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10751;_},uu____10752)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10769 -> tm1
                                   else
                                     (let uu____10779 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10779 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10799 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10808 -> tm1)
let maybe_simplify:
  'Auu____10815 'Auu____10816 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10816) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10815 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10859 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10859
           then
             let uu____10860 = FStar_Syntax_Print.term_to_string tm in
             let uu____10861 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10860 uu____10861
           else ());
          tm'
let is_norm_request:
  'Auu____10867 .
    FStar_Syntax_Syntax.term -> 'Auu____10867 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10880 =
        let uu____10887 =
          let uu____10888 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10888.FStar_Syntax_Syntax.n in
        (uu____10887, args) in
      match uu____10880 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10894::uu____10895::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10899::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10904::uu____10905::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10908 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___81_10919  ->
    match uu___81_10919 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10925 =
          let uu____10928 =
            let uu____10929 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10929 in
          [uu____10928] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10925
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10945 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10945) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10983 =
          let uu____10986 =
            let uu____10991 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10991 s in
          FStar_All.pipe_right uu____10986 FStar_Util.must in
        FStar_All.pipe_right uu____10983 tr_norm_steps in
      match args with
      | uu____11016::(tm,uu____11018)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11041)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11056)::uu____11057::(tm,uu____11059)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11099 =
              let uu____11102 = full_norm steps in parse_steps uu____11102 in
            Beta :: uu____11099 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11111 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___82_11128  ->
    match uu___82_11128 with
    | (App
        (uu____11131,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11132;
                       FStar_Syntax_Syntax.vars = uu____11133;_},uu____11134,uu____11135))::uu____11136
        -> true
    | uu____11143 -> false
let firstn:
  'Auu____11149 .
    Prims.int ->
      'Auu____11149 Prims.list ->
        ('Auu____11149 Prims.list,'Auu____11149 Prims.list)
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
          (uu____11185,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11186;
                         FStar_Syntax_Syntax.vars = uu____11187;_},uu____11188,uu____11189))::uu____11190
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11197 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            (let uu____11339 =
               FStar_TypeChecker_Env.debug cfg.tcenv
                 (FStar_Options.Other "NormDelayed") in
             if uu____11339
             then
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____11340 ->
                   let uu____11365 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11365
               | uu____11366 -> ()
             else ());
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11375  ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               let uu____11377 = FStar_Syntax_Print.tag_of_term t2 in
               let uu____11378 = FStar_Syntax_Print.term_to_string t2 in
               let uu____11379 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11386 =
                 let uu____11387 =
                   let uu____11390 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11390 in
                 stack_to_string uu____11387 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11377 uu____11378 uu____11379 uu____11386);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11413 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11414 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11415;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11416;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11419;
                 FStar_Syntax_Syntax.fv_delta = uu____11420;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11421;
                 FStar_Syntax_Syntax.fv_delta = uu____11422;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11423);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11431 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11431 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11437  ->
                     let uu____11438 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11439 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11438 uu____11439);
                if b
                then
                  (let uu____11440 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11440 t1 fv)
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
                 let uu___119_11479 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___119_11479.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___119_11479.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11512 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11512) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___120_11520 = cfg in
                 let uu____11521 =
                   FStar_List.filter
                     (fun uu___83_11524  ->
                        match uu___83_11524 with
                        | UnfoldOnly uu____11525 -> false
                        | NoDeltaSteps  -> false
                        | uu____11528 -> true) cfg.steps in
                 {
                   steps = uu____11521;
                   tcenv = (uu___120_11520.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___120_11520.primitive_steps);
                   strong = (uu___120_11520.strong);
                   memoize_lazy = (uu___120_11520.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____11529 = get_norm_request (norm cfg' env []) args in
               (match uu____11529 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11545 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___84_11550  ->
                                match uu___84_11550 with
                                | UnfoldUntil uu____11551 -> true
                                | UnfoldOnly uu____11552 -> true
                                | uu____11555 -> false)) in
                      if uu____11545
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___121_11560 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___121_11560.tcenv);
                        delta_level;
                        primitive_steps = (uu___121_11560.primitive_steps);
                        strong = (uu___121_11560.strong);
                        memoize_lazy = (uu___121_11560.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11567 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11567
                      then
                        let uu____11570 =
                          let uu____11571 =
                            let uu____11576 = FStar_Util.now () in
                            (t1, uu____11576) in
                          Debug uu____11571 in
                        uu____11570 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11580 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11580
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11587 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11587
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11590 =
                      let uu____11597 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11597, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11590 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___85_11610  ->
                         match uu___85_11610 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11613 =
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
                 if uu____11613
                 then false
                 else
                   (let uu____11615 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___86_11622  ->
                              match uu___86_11622 with
                              | UnfoldOnly uu____11623 -> true
                              | UnfoldAttr uu____11626 -> true
                              | uu____11627 -> false)) in
                    match uu____11615 with
                    | FStar_Pervasives_Native.Some uu____11628 ->
                        let attr_eq a a' =
                          let uu____11636 = FStar_Syntax_Util.eq_tm a a' in
                          match uu____11636 with
                          | FStar_Syntax_Util.Equal  -> true
                          | uu____11637 -> false in
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
                                      let uu____11647 =
                                        FStar_TypeChecker_Env.lookup_attrs_of_lid
                                          cfg.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      (match uu____11647 with
                                       | FStar_Pervasives_Native.Some attrs
                                           ->
                                           acc ||
                                             (FStar_Util.for_some
                                                (attr_eq attr) attrs)
                                       | uu____11657 -> acc)
                                  | uu____11662 -> acc) false cfg.steps)
                    | uu____11663 -> should_delta) in
               (log cfg
                  (fun uu____11671  ->
                     let uu____11672 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11673 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11674 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11672 uu____11673 uu____11674);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11677 = lookup_bvar env x in
               (match uu____11677 with
                | Univ uu____11680 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11729 = FStar_ST.op_Bang r in
                      (match uu____11729 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11847  ->
                                 let uu____11848 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11849 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11848
                                   uu____11849);
                            (let uu____11850 =
                               let uu____11851 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11851.FStar_Syntax_Syntax.n in
                             match uu____11850 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11854 ->
                                 norm cfg env2 stack t'
                             | uu____11871 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11941)::uu____11942 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11951)::uu____11952 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11962,uu____11963))::stack_rest ->
                    (match c with
                     | Univ uu____11967 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11976 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11997  ->
                                    let uu____11998 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11998);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12038  ->
                                    let uu____12039 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12039);
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
                       (fun uu____12117  ->
                          let uu____12118 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12118);
                     norm cfg env stack1 t1)
                | (Debug uu____12119)::uu____12120 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12127 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12127
                    else
                      (let uu____12129 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12129 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12171  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12199 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12199
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12209 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12209)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12214 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12214.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12214.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12215 -> lopt in
                           (log cfg
                              (fun uu____12221  ->
                                 let uu____12222 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12222);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12231 = cfg in
                               {
                                 steps = (uu___123_12231.steps);
                                 tcenv = (uu___123_12231.tcenv);
                                 delta_level = (uu___123_12231.delta_level);
                                 primitive_steps =
                                   (uu___123_12231.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12231.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12231.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12242)::uu____12243 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12250 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12250
                    else
                      (let uu____12252 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12252 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12294  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12322 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12322
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12332 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12332)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12337 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12337.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12337.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12338 -> lopt in
                           (log cfg
                              (fun uu____12344  ->
                                 let uu____12345 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12345);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12354 = cfg in
                               {
                                 steps = (uu___123_12354.steps);
                                 tcenv = (uu___123_12354.tcenv);
                                 delta_level = (uu___123_12354.delta_level);
                                 primitive_steps =
                                   (uu___123_12354.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12354.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12354.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12365)::uu____12366 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12377 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12377
                    else
                      (let uu____12379 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12379 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12421  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12449 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12449
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12459 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12459)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12464 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12464.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12464.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12465 -> lopt in
                           (log cfg
                              (fun uu____12471  ->
                                 let uu____12472 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12472);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12481 = cfg in
                               {
                                 steps = (uu___123_12481.steps);
                                 tcenv = (uu___123_12481.tcenv);
                                 delta_level = (uu___123_12481.delta_level);
                                 primitive_steps =
                                   (uu___123_12481.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12481.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12481.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12492)::uu____12493 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12504 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12504
                    else
                      (let uu____12506 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12506 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12548  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12576 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12576
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12586 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12586)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12591 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12591.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12591.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12592 -> lopt in
                           (log cfg
                              (fun uu____12598  ->
                                 let uu____12599 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12599);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12608 = cfg in
                               {
                                 steps = (uu___123_12608.steps);
                                 tcenv = (uu___123_12608.tcenv);
                                 delta_level = (uu___123_12608.delta_level);
                                 primitive_steps =
                                   (uu___123_12608.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12608.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12608.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12619)::uu____12620 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12635 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12635
                    else
                      (let uu____12637 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12637 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12679  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12707 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12707
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12717 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12717)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12722 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12722.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12722.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12723 -> lopt in
                           (log cfg
                              (fun uu____12729  ->
                                 let uu____12730 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12730);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12739 = cfg in
                               {
                                 steps = (uu___123_12739.steps);
                                 tcenv = (uu___123_12739.tcenv);
                                 delta_level = (uu___123_12739.delta_level);
                                 primitive_steps =
                                   (uu___123_12739.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12739.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12739.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12750 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12750
                    else
                      (let uu____12752 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12752 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12794  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12822 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12822
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12832 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12832)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12837 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12837.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12837.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12838 -> lopt in
                           (log cfg
                              (fun uu____12844  ->
                                 let uu____12845 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12845);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12854 = cfg in
                               {
                                 steps = (uu___123_12854.steps);
                                 tcenv = (uu___123_12854.tcenv);
                                 delta_level = (uu___123_12854.delta_level);
                                 primitive_steps =
                                   (uu___123_12854.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12854.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12854.normalize_pure_lets)
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
                      (fun uu____12903  ->
                         fun stack1  ->
                           match uu____12903 with
                           | (a,aq) ->
                               let uu____12915 =
                                 let uu____12916 =
                                   let uu____12923 =
                                     let uu____12924 =
                                       let uu____12955 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12955, false) in
                                     Clos uu____12924 in
                                   (uu____12923, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12916 in
                               uu____12915 :: stack1) args) in
               (log cfg
                  (fun uu____13039  ->
                     let uu____13040 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13040);
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
                             ((let uu___124_13076 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___124_13076.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___124_13076.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13077 ->
                      let uu____13082 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13082)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13085 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13085 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13116 =
                          let uu____13117 =
                            let uu____13124 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___125_13126 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___125_13126.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___125_13126.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13124) in
                          FStar_Syntax_Syntax.Tm_refine uu____13117 in
                        mk uu____13116 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13145 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13145
               else
                 (let uu____13147 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13147 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13155 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13179  -> dummy :: env1) env) in
                        norm_comp cfg uu____13155 c1 in
                      let t2 =
                        let uu____13201 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13201 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13260)::uu____13261 ->
                    (log cfg
                       (fun uu____13272  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13273)::uu____13274 ->
                    (log cfg
                       (fun uu____13285  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13286,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13287;
                                   FStar_Syntax_Syntax.vars = uu____13288;_},uu____13289,uu____13290))::uu____13291
                    ->
                    (log cfg
                       (fun uu____13300  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13301)::uu____13302 ->
                    (log cfg
                       (fun uu____13313  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13314 ->
                    (log cfg
                       (fun uu____13317  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13321  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13338 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13338
                         | FStar_Util.Inr c ->
                             let uu____13346 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13346 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13359 =
                               let uu____13360 =
                                 let uu____13387 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13387, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13360 in
                             mk uu____13359 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13406 ->
                           let uu____13407 =
                             let uu____13408 =
                               let uu____13409 =
                                 let uu____13436 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13436, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13409 in
                             mk uu____13408 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13407))))
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
                         let uu____13546 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13546 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___126_13566 = cfg in
                               let uu____13567 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___126_13566.steps);
                                 tcenv = uu____13567;
                                 delta_level = (uu___126_13566.delta_level);
                                 primitive_steps =
                                   (uu___126_13566.primitive_steps);
                                 strong = (uu___126_13566.strong);
                                 memoize_lazy = (uu___126_13566.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___126_13566.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____13572 =
                                 let uu____13573 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13573 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13572 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___127_13576 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___127_13576.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___127_13576.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13577 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13577
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13588,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13589;
                               FStar_Syntax_Syntax.lbunivs = uu____13590;
                               FStar_Syntax_Syntax.lbtyp = uu____13591;
                               FStar_Syntax_Syntax.lbeff = uu____13592;
                               FStar_Syntax_Syntax.lbdef = uu____13593;_}::uu____13594),uu____13595)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13631 =
                 (let uu____13634 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13634) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13636 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13636))) in
               if uu____13631
               then
                 let binder =
                   let uu____13638 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13638 in
                 let env1 =
                   let uu____13648 =
                     let uu____13655 =
                       let uu____13656 =
                         let uu____13687 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13687,
                           false) in
                       Clos uu____13656 in
                     ((FStar_Pervasives_Native.Some binder), uu____13655) in
                   uu____13648 :: env in
                 (log cfg
                    (fun uu____13780  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13782 =
                    let uu____13787 =
                      let uu____13788 =
                        let uu____13789 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13789
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13788] in
                    FStar_Syntax_Subst.open_term uu____13787 body in
                  match uu____13782 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13798  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13806 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13806 in
                          FStar_Util.Inl
                            (let uu___128_13816 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___128_13816.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___128_13816.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13819  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___129_13821 = lb in
                           let uu____13822 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___129_13821.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___129_13821.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13822
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13857  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___130_13880 = cfg in
                           {
                             steps = (uu___130_13880.steps);
                             tcenv = (uu___130_13880.tcenv);
                             delta_level = (uu___130_13880.delta_level);
                             primitive_steps =
                               (uu___130_13880.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___130_13880.memoize_lazy);
                             normalize_pure_lets =
                               (uu___130_13880.normalize_pure_lets)
                           } in
                         log cfg1
                           (fun uu____13883  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n");
                         norm cfg1 env'
                           ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13900 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13900 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13936 =
                               let uu___131_13937 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_13937.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_13937.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13936 in
                           let uu____13938 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13938 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13964 =
                                   FStar_List.map (fun uu____13980  -> dummy)
                                     lbs1 in
                                 let uu____13981 =
                                   let uu____13990 =
                                     FStar_List.map
                                       (fun uu____14010  -> dummy) xs1 in
                                   FStar_List.append uu____13990 env in
                                 FStar_List.append uu____13964 uu____13981 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14034 =
                                       let uu___132_14035 = rc in
                                       let uu____14036 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___132_14035.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14036;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___132_14035.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14034
                                 | uu____14043 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___133_14047 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___133_14047.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___133_14047.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14057 =
                        FStar_List.map (fun uu____14073  -> dummy) lbs2 in
                      FStar_List.append uu____14057 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14081 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14081 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___134_14097 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___134_14097.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___134_14097.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14124 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14124
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14143 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14219  ->
                        match uu____14219 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___135_14340 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___135_14340.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___135_14340.FStar_Syntax_Syntax.sort)
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
               (match uu____14143 with
                | (rec_env,memos,uu____14553) ->
                    let uu____14606 =
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
                             let uu____14917 =
                               let uu____14924 =
                                 let uu____14925 =
                                   let uu____14956 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14956, false) in
                                 Clos uu____14925 in
                               (FStar_Pervasives_Native.None, uu____14924) in
                             uu____14917 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15066  ->
                     let uu____15067 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15067);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15089 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15091::uu____15092 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15097) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15098 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15129 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15143 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15143
                              | uu____15154 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15158 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15184 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15202 ->
                    let uu____15219 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains CheckNoUvars) in
                    if uu____15219
                    then
                      let uu____15220 =
                        let uu____15221 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____15222 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15221 uu____15222 in
                      failwith uu____15220
                    else rebuild cfg env stack t2
                | uu____15224 -> norm cfg env stack t2))
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
              let uu____15233 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15233 in
            let uu____15234 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15234 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15247  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15258  ->
                      let uu____15259 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15260 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15259
                        uu____15260);
                 (let t1 =
                    let uu____15262 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15264 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15264) in
                    if uu____15262
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
                    | (UnivArgs (us',uu____15274))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15329 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15332 ->
                        let uu____15335 =
                          let uu____15336 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15336 in
                        failwith uu____15335
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
                let uu____15357 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15357
                then
                  let uu___136_15358 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___136_15358.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___136_15358.primitive_steps);
                    strong = (uu___136_15358.strong);
                    memoize_lazy = (uu___136_15358.memoize_lazy);
                    normalize_pure_lets =
                      (uu___136_15358.normalize_pure_lets)
                  }
                else
                  (let uu___137_15360 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___137_15360.tcenv);
                     delta_level = (uu___137_15360.delta_level);
                     primitive_steps = (uu___137_15360.primitive_steps);
                     strong = (uu___137_15360.strong);
                     memoize_lazy = (uu___137_15360.memoize_lazy);
                     normalize_pure_lets =
                       (uu___137_15360.normalize_pure_lets)
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
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____15389  ->
                     let uu____15390 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15391 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15390
                       uu____15391);
                (let uu____15392 =
                   let uu____15393 = FStar_Syntax_Subst.compress head2 in
                   uu____15393.FStar_Syntax_Syntax.n in
                 match uu____15392 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15411 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15411 with
                      | (uu____15412,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15418 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15426 =
                                   let uu____15427 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15427.FStar_Syntax_Syntax.n in
                                 match uu____15426 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15433,uu____15434))
                                     ->
                                     let uu____15443 =
                                       let uu____15444 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15444.FStar_Syntax_Syntax.n in
                                     (match uu____15443 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15450,msrc,uu____15452))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15461 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15461
                                      | uu____15462 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15463 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15464 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15464 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___138_15469 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___138_15469.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___138_15469.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___138_15469.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15470 = FStar_List.tl stack in
                                    let uu____15471 =
                                      let uu____15472 =
                                        let uu____15475 =
                                          let uu____15476 =
                                            let uu____15489 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15489) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15476 in
                                        FStar_Syntax_Syntax.mk uu____15475 in
                                      uu____15472
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15470 uu____15471
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15505 =
                                      let uu____15506 = is_return body in
                                      match uu____15506 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15510;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15511;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15516 -> false in
                                    if uu____15505
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
                                         let uu____15539 =
                                           let uu____15542 =
                                             let uu____15543 =
                                               let uu____15560 =
                                                 let uu____15563 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15563] in
                                               (uu____15560, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15543 in
                                           FStar_Syntax_Syntax.mk uu____15542 in
                                         uu____15539
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15579 =
                                           let uu____15580 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15580.FStar_Syntax_Syntax.n in
                                         match uu____15579 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15586::uu____15587::[])
                                             ->
                                             let uu____15594 =
                                               let uu____15597 =
                                                 let uu____15598 =
                                                   let uu____15605 =
                                                     let uu____15608 =
                                                       let uu____15609 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15609 in
                                                     let uu____15610 =
                                                       let uu____15613 =
                                                         let uu____15614 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15614 in
                                                       [uu____15613] in
                                                     uu____15608 ::
                                                       uu____15610 in
                                                   (bind1, uu____15605) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15598 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15597 in
                                             uu____15594
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15622 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15628 =
                                           let uu____15631 =
                                             let uu____15632 =
                                               let uu____15647 =
                                                 let uu____15650 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15651 =
                                                   let uu____15654 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15655 =
                                                     let uu____15658 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15659 =
                                                       let uu____15662 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15663 =
                                                         let uu____15666 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15667 =
                                                           let uu____15670 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15670] in
                                                         uu____15666 ::
                                                           uu____15667 in
                                                       uu____15662 ::
                                                         uu____15663 in
                                                     uu____15658 ::
                                                       uu____15659 in
                                                   uu____15654 :: uu____15655 in
                                                 uu____15650 :: uu____15651 in
                                               (bind_inst, uu____15647) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15632 in
                                           FStar_Syntax_Syntax.mk uu____15631 in
                                         uu____15628
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15681  ->
                                            let uu____15682 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15682);
                                       (let uu____15683 = FStar_List.tl stack in
                                        norm cfg env uu____15683 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15707 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15707 with
                      | (uu____15708,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15743 =
                                  let uu____15744 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15744.FStar_Syntax_Syntax.n in
                                match uu____15743 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15750) -> t2
                                | uu____15755 -> head3 in
                              let uu____15756 =
                                let uu____15757 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15757.FStar_Syntax_Syntax.n in
                              match uu____15756 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15763 -> FStar_Pervasives_Native.None in
                            let uu____15764 = maybe_extract_fv head3 in
                            match uu____15764 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15774 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15774
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15779 = maybe_extract_fv head4 in
                                  match uu____15779 with
                                  | FStar_Pervasives_Native.Some uu____15784
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15785 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15790 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15805 =
                              match uu____15805 with
                              | (e,q) ->
                                  let uu____15812 =
                                    let uu____15813 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15813.FStar_Syntax_Syntax.n in
                                  (match uu____15812 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15828 -> false) in
                            let uu____15829 =
                              let uu____15830 =
                                let uu____15837 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15837 :: args in
                              FStar_Util.for_some is_arg_impure uu____15830 in
                            if uu____15829
                            then
                              let uu____15842 =
                                let uu____15843 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15843 in
                              failwith uu____15842
                            else ());
                           (let uu____15845 = maybe_unfold_action head_app in
                            match uu____15845 with
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
                                let uu____15882 = FStar_List.tl stack in
                                norm cfg env uu____15882 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15884) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15908 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15908 in
                     (log cfg
                        (fun uu____15912  ->
                           let uu____15913 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15913);
                      (let uu____15914 = FStar_List.tl stack in
                       norm cfg env uu____15914 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15916) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16041  ->
                               match uu____16041 with
                               | (pat,wopt,tm) ->
                                   let uu____16089 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____16089))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16121 = FStar_List.tl stack in
                     norm cfg env uu____16121 tm
                 | uu____16122 -> fallback ())
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
              (fun uu____16136  ->
                 let uu____16137 = FStar_Ident.string_of_lid msrc in
                 let uu____16138 = FStar_Ident.string_of_lid mtgt in
                 let uu____16139 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16137
                   uu____16138 uu____16139);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16141 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16141 with
               | (uu____16142,return_repr) ->
                   let return_inst =
                     let uu____16151 =
                       let uu____16152 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16152.FStar_Syntax_Syntax.n in
                     match uu____16151 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16158::[]) ->
                         let uu____16165 =
                           let uu____16168 =
                             let uu____16169 =
                               let uu____16176 =
                                 let uu____16179 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16179] in
                               (return_tm, uu____16176) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16169 in
                           FStar_Syntax_Syntax.mk uu____16168 in
                         uu____16165 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16187 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16190 =
                     let uu____16193 =
                       let uu____16194 =
                         let uu____16209 =
                           let uu____16212 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16213 =
                             let uu____16216 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16216] in
                           uu____16212 :: uu____16213 in
                         (return_inst, uu____16209) in
                       FStar_Syntax_Syntax.Tm_app uu____16194 in
                     FStar_Syntax_Syntax.mk uu____16193 in
                   uu____16190 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16225 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16225 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16228 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16228
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16229;
                     FStar_TypeChecker_Env.mtarget = uu____16230;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16231;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16246;
                     FStar_TypeChecker_Env.mtarget = uu____16247;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16248;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16272 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16273 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16272 t FStar_Syntax_Syntax.tun uu____16273)
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
                (fun uu____16329  ->
                   match uu____16329 with
                   | (a,imp) ->
                       let uu____16340 = norm cfg env [] a in
                       (uu____16340, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___139_16354 = comp in
            let uu____16355 =
              let uu____16356 =
                let uu____16365 = norm cfg env [] t in
                let uu____16366 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16365, uu____16366) in
              FStar_Syntax_Syntax.Total uu____16356 in
            {
              FStar_Syntax_Syntax.n = uu____16355;
              FStar_Syntax_Syntax.pos =
                (uu___139_16354.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_16354.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___140_16381 = comp in
            let uu____16382 =
              let uu____16383 =
                let uu____16392 = norm cfg env [] t in
                let uu____16393 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16392, uu____16393) in
              FStar_Syntax_Syntax.GTotal uu____16383 in
            {
              FStar_Syntax_Syntax.n = uu____16382;
              FStar_Syntax_Syntax.pos =
                (uu___140_16381.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___140_16381.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16445  ->
                      match uu____16445 with
                      | (a,i) ->
                          let uu____16456 = norm cfg env [] a in
                          (uu____16456, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___87_16467  ->
                      match uu___87_16467 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16471 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16471
                      | f -> f)) in
            let uu___141_16475 = comp in
            let uu____16476 =
              let uu____16477 =
                let uu___142_16478 = ct in
                let uu____16479 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16480 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16483 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16479;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___142_16478.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16480;
                  FStar_Syntax_Syntax.effect_args = uu____16483;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16477 in
            {
              FStar_Syntax_Syntax.n = uu____16476;
              FStar_Syntax_Syntax.pos =
                (uu___141_16475.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___141_16475.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16494  ->
        match uu____16494 with
        | (x,imp) ->
            let uu____16497 =
              let uu___143_16498 = x in
              let uu____16499 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___143_16498.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___143_16498.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16499
              } in
            (uu____16497, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16505 =
          FStar_List.fold_left
            (fun uu____16523  ->
               fun b  ->
                 match uu____16523 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16505 with | (nbs,uu____16563) -> FStar_List.rev nbs
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
            let uu____16579 =
              let uu___144_16580 = rc in
              let uu____16581 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___144_16580.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16581;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___144_16580.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16579
        | uu____16588 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16601  ->
               let uu____16602 = FStar_Syntax_Print.tag_of_term t in
               let uu____16603 = FStar_Syntax_Print.term_to_string t in
               let uu____16604 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16611 =
                 let uu____16612 =
                   let uu____16615 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16615 in
                 stack_to_string uu____16612 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16602 uu____16603 uu____16604 uu____16611);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16644 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16644
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16646 =
                     let uu____16647 =
                       let uu____16648 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16648 in
                     FStar_Util.string_of_int uu____16647 in
                   let uu____16653 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16654 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16646 uu____16653 uu____16654
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16708  ->
                     let uu____16709 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16709);
                rebuild cfg env stack1 t)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____16745 =
                 let uu___145_16746 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___145_16746.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___145_16746.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16745
           | (Arg (Univ uu____16747,uu____16748,uu____16749))::uu____16750 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16753,uu____16754))::uu____16755 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16771),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16824  ->
                     let uu____16825 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16825);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack1 t1
                   else
                     (let stack2 = (App (env, t, aq, r)) :: stack1 in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____16835 = FStar_ST.op_Bang m in
                   match uu____16835 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack1 t1
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack1 in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____16972,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____17019 =
                 log cfg
                   (fun uu____17023  ->
                      let uu____17024 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____17024);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____17028 =
                 let uu____17029 = FStar_Syntax_Subst.compress t in
                 uu____17029.FStar_Syntax_Syntax.n in
               (match uu____17028 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____17056 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____17056 in
                    (log cfg
                       (fun uu____17060  ->
                          let uu____17061 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____17061);
                     (let uu____17062 = FStar_List.tl stack in
                      norm cfg env1 uu____17062 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____17063);
                       FStar_Syntax_Syntax.pos = uu____17064;
                       FStar_Syntax_Syntax.vars = uu____17065;_},(e,uu____17067)::[])
                    -> norm cfg env1 stack' e
                | uu____17096 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17107 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17107
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17119  ->
                     let uu____17120 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17120);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17125 =
                   log cfg
                     (fun uu____17130  ->
                        let uu____17131 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17132 =
                          let uu____17133 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17150  ->
                                    match uu____17150 with
                                    | (p,uu____17160,uu____17161) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17133
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17131 uu____17132);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___88_17178  ->
                                match uu___88_17178 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17179 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___146_17183 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___146_17183.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___146_17183.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___146_17183.memoize_lazy);
                        normalize_pure_lets =
                          (uu___146_17183.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17215 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17236 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17296  ->
                                    fun uu____17297  ->
                                      match (uu____17296, uu____17297) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17388 = norm_pat env3 p1 in
                                          (match uu____17388 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17236 with
                           | (pats1,env3) ->
                               ((let uu___147_17470 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___147_17470.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___148_17489 = x in
                            let uu____17490 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17489.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17489.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17490
                            } in
                          ((let uu___149_17504 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___149_17504.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___150_17515 = x in
                            let uu____17516 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___150_17515.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___150_17515.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17516
                            } in
                          ((let uu___151_17530 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___151_17530.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___152_17546 = x in
                            let uu____17547 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_17546.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_17546.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17547
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___153_17554 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___153_17554.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17564 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17578 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17578 with
                                  | (p,wopt,e) ->
                                      let uu____17598 = norm_pat env1 p in
                                      (match uu____17598 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17623 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17623 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17629 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17629) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17639) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17644 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17645;
                         FStar_Syntax_Syntax.fv_delta = uu____17646;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17647;
                         FStar_Syntax_Syntax.fv_delta = uu____17648;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17649);_}
                       -> true
                   | uu____17656 -> false in
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
                   let uu____17801 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17801 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17888 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17927 ->
                                 let uu____17928 =
                                   let uu____17929 = is_cons head1 in
                                   Prims.op_Negation uu____17929 in
                                 FStar_Util.Inr uu____17928)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17954 =
                              let uu____17955 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17955.FStar_Syntax_Syntax.n in
                            (match uu____17954 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17973 ->
                                 let uu____17974 =
                                   let uu____17975 = is_cons head1 in
                                   Prims.op_Negation uu____17975 in
                                 FStar_Util.Inr uu____17974))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18044)::rest_a,(p1,uu____18047)::rest_p) ->
                       let uu____18091 = matches_pat t1 p1 in
                       (match uu____18091 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18140 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18246 = matches_pat scrutinee1 p1 in
                       (match uu____18246 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18286  ->
                                  let uu____18287 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18288 =
                                    let uu____18289 =
                                      FStar_List.map
                                        (fun uu____18299  ->
                                           match uu____18299 with
                                           | (uu____18304,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18289
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18287 uu____18288);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18335  ->
                                       match uu____18335 with
                                       | (bv,t1) ->
                                           let uu____18358 =
                                             let uu____18365 =
                                               let uu____18368 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18368 in
                                             let uu____18369 =
                                               let uu____18370 =
                                                 let uu____18401 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18401, false) in
                                               Clos uu____18370 in
                                             (uu____18365, uu____18369) in
                                           uu____18358 :: env2) env1 s in
                              let uu____18518 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18518))) in
                 let uu____18519 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18519
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___89_18540  ->
                match uu___89_18540 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18544 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18550 -> d in
      let uu____18553 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18555 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations) in
           Prims.op_Negation uu____18555) in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18553
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
            let uu___154_18580 = config s e in
            {
              steps = (uu___154_18580.steps);
              tcenv = (uu___154_18580.tcenv);
              delta_level = (uu___154_18580.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___154_18580.strong);
              memoize_lazy = (uu___154_18580.memoize_lazy);
              normalize_pure_lets = (uu___154_18580.normalize_pure_lets)
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
      fun t  -> let uu____18605 = config s e in norm_comp uu____18605 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18618 = config [] env in norm_universe uu____18618 [] u
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
        let uu____18636 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18636 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18643 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___155_18662 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___155_18662.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___155_18662.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18669 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18669
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
                  let uu___156_18678 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___156_18678.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___156_18678.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___156_18678.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___157_18680 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___157_18680.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___157_18680.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___157_18680.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___157_18680.FStar_Syntax_Syntax.flags)
                  } in
            let uu___158_18681 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___158_18681.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___158_18681.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18683 -> c
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
        let uu____18695 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18695 in
      let uu____18702 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18702
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18706  ->
                 let uu____18707 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18707)
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
            ((let uu____18724 =
                let uu____18729 =
                  let uu____18730 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18730 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18729) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18724);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18741 = config [AllowUnboundUniverses] env in
          norm_comp uu____18741 [] c
        with
        | e ->
            ((let uu____18754 =
                let uu____18759 =
                  let uu____18760 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18760 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18759) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18754);
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
                   let uu____18797 =
                     let uu____18798 =
                       let uu____18805 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18805) in
                     FStar_Syntax_Syntax.Tm_refine uu____18798 in
                   mk uu____18797 t01.FStar_Syntax_Syntax.pos
               | uu____18810 -> t2)
          | uu____18811 -> t2 in
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
        let uu____18851 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18851 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18880 ->
                 let uu____18887 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18887 with
                  | (actuals,uu____18897,uu____18898) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18912 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18912 with
                         | (binders,args) ->
                             let uu____18929 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18929
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
      | uu____18937 ->
          let uu____18938 = FStar_Syntax_Util.head_and_args t in
          (match uu____18938 with
           | (head1,args) ->
               let uu____18975 =
                 let uu____18976 = FStar_Syntax_Subst.compress head1 in
                 uu____18976.FStar_Syntax_Syntax.n in
               (match uu____18975 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18979,thead) ->
                    let uu____19005 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19005 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19047 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___163_19055 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___163_19055.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___163_19055.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___163_19055.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___163_19055.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___163_19055.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___163_19055.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___163_19055.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___163_19055.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___163_19055.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___163_19055.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___163_19055.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___163_19055.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___163_19055.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___163_19055.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___163_19055.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___163_19055.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___163_19055.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___163_19055.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___163_19055.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___163_19055.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___163_19055.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___163_19055.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___163_19055.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___163_19055.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___163_19055.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___163_19055.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___163_19055.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___163_19055.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___163_19055.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___163_19055.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___163_19055.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___163_19055.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19047 with
                            | (uu____19056,ty,uu____19058) ->
                                eta_expand_with_type env t ty))
                | uu____19059 ->
                    let uu____19060 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___164_19068 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___164_19068.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___164_19068.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___164_19068.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___164_19068.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___164_19068.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___164_19068.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___164_19068.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___164_19068.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___164_19068.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___164_19068.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___164_19068.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___164_19068.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___164_19068.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___164_19068.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___164_19068.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___164_19068.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___164_19068.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___164_19068.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___164_19068.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___164_19068.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___164_19068.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___164_19068.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___164_19068.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___164_19068.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___164_19068.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___164_19068.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___164_19068.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___164_19068.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___164_19068.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___164_19068.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___164_19068.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___164_19068.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19060 with
                     | (uu____19069,ty,uu____19071) ->
                         eta_expand_with_type env t ty)))
let rec elim_delayed_subst_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___165_19128 = x in
      let uu____19129 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___165_19128.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___165_19128.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____19129
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____19132 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____19157 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____19158 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____19159 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____19160 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____19167 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____19168 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___166_19196 = rc in
          let uu____19197 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____19204 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___166_19196.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____19197;
            FStar_Syntax_Syntax.residual_flags = uu____19204
          } in
        let uu____19207 =
          let uu____19208 =
            let uu____19225 = elim_delayed_subst_binders bs in
            let uu____19232 = elim_delayed_subst_term t2 in
            let uu____19233 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____19225, uu____19232, uu____19233) in
          FStar_Syntax_Syntax.Tm_abs uu____19208 in
        mk1 uu____19207
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____19262 =
          let uu____19263 =
            let uu____19276 = elim_delayed_subst_binders bs in
            let uu____19283 = elim_delayed_subst_comp c in
            (uu____19276, uu____19283) in
          FStar_Syntax_Syntax.Tm_arrow uu____19263 in
        mk1 uu____19262
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____19296 =
          let uu____19297 =
            let uu____19304 = elim_bv bv in
            let uu____19305 = elim_delayed_subst_term phi in
            (uu____19304, uu____19305) in
          FStar_Syntax_Syntax.Tm_refine uu____19297 in
        mk1 uu____19296
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____19328 =
          let uu____19329 =
            let uu____19344 = elim_delayed_subst_term t2 in
            let uu____19345 = elim_delayed_subst_args args in
            (uu____19344, uu____19345) in
          FStar_Syntax_Syntax.Tm_app uu____19329 in
        mk1 uu____19328
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___167_19409 = p in
              let uu____19410 =
                let uu____19411 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____19411 in
              {
                FStar_Syntax_Syntax.v = uu____19410;
                FStar_Syntax_Syntax.p =
                  (uu___167_19409.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___168_19413 = p in
              let uu____19414 =
                let uu____19415 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____19415 in
              {
                FStar_Syntax_Syntax.v = uu____19414;
                FStar_Syntax_Syntax.p =
                  (uu___168_19413.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___169_19422 = p in
              let uu____19423 =
                let uu____19424 =
                  let uu____19431 = elim_bv x in
                  let uu____19432 = elim_delayed_subst_term t0 in
                  (uu____19431, uu____19432) in
                FStar_Syntax_Syntax.Pat_dot_term uu____19424 in
              {
                FStar_Syntax_Syntax.v = uu____19423;
                FStar_Syntax_Syntax.p =
                  (uu___169_19422.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___170_19451 = p in
              let uu____19452 =
                let uu____19453 =
                  let uu____19466 =
                    FStar_List.map
                      (fun uu____19489  ->
                         match uu____19489 with
                         | (x,b) ->
                             let uu____19502 = elim_pat x in (uu____19502, b))
                      pats in
                  (fv, uu____19466) in
                FStar_Syntax_Syntax.Pat_cons uu____19453 in
              {
                FStar_Syntax_Syntax.v = uu____19452;
                FStar_Syntax_Syntax.p =
                  (uu___170_19451.FStar_Syntax_Syntax.p)
              }
          | uu____19515 -> p in
        let elim_branch uu____19537 =
          match uu____19537 with
          | (pat,wopt,t3) ->
              let uu____19563 = elim_pat pat in
              let uu____19566 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____19569 = elim_delayed_subst_term t3 in
              (uu____19563, uu____19566, uu____19569) in
        let uu____19574 =
          let uu____19575 =
            let uu____19598 = elim_delayed_subst_term t2 in
            let uu____19599 = FStar_List.map elim_branch branches in
            (uu____19598, uu____19599) in
          FStar_Syntax_Syntax.Tm_match uu____19575 in
        mk1 uu____19574
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____19708 =
          match uu____19708 with
          | (tc,topt) ->
              let uu____19743 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____19753 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____19753
                | FStar_Util.Inr c ->
                    let uu____19755 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____19755 in
              let uu____19756 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____19743, uu____19756) in
        let uu____19765 =
          let uu____19766 =
            let uu____19793 = elim_delayed_subst_term t2 in
            let uu____19794 = elim_ascription a in
            (uu____19793, uu____19794, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____19766 in
        mk1 uu____19765
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___171_19839 = lb in
          let uu____19840 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____19843 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___171_19839.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___171_19839.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____19840;
            FStar_Syntax_Syntax.lbeff =
              (uu___171_19839.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____19843
          } in
        let uu____19846 =
          let uu____19847 =
            let uu____19860 =
              let uu____19867 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____19867) in
            let uu____19876 = elim_delayed_subst_term t2 in
            (uu____19860, uu____19876) in
          FStar_Syntax_Syntax.Tm_let uu____19847 in
        mk1 uu____19846
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____19909 =
          let uu____19910 =
            let uu____19927 = elim_delayed_subst_term t2 in (uv, uu____19927) in
          FStar_Syntax_Syntax.Tm_uvar uu____19910 in
        mk1 uu____19909
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____19944 =
          let uu____19945 =
            let uu____19952 = elim_delayed_subst_term t2 in
            let uu____19953 = elim_delayed_subst_meta md in
            (uu____19952, uu____19953) in
          FStar_Syntax_Syntax.Tm_meta uu____19945 in
        mk1 uu____19944
and elim_delayed_subst_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___90_19960  ->
         match uu___90_19960 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____19964 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____19964
         | f -> f) flags1
and elim_delayed_subst_comp:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____19985 =
          let uu____19986 =
            let uu____19995 = elim_delayed_subst_term t in
            (uu____19995, uopt) in
          FStar_Syntax_Syntax.Total uu____19986 in
        mk1 uu____19985
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____20008 =
          let uu____20009 =
            let uu____20018 = elim_delayed_subst_term t in
            (uu____20018, uopt) in
          FStar_Syntax_Syntax.GTotal uu____20009 in
        mk1 uu____20008
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___172_20023 = ct in
          let uu____20024 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____20027 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____20036 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___172_20023.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___172_20023.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____20024;
            FStar_Syntax_Syntax.effect_args = uu____20027;
            FStar_Syntax_Syntax.flags = uu____20036
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and elim_delayed_subst_meta:
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata =
  fun uu___91_20039  ->
    match uu___91_20039 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____20051 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____20051
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____20084 =
          let uu____20091 = elim_delayed_subst_term t in (m, uu____20091) in
        FStar_Syntax_Syntax.Meta_monadic uu____20084
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____20099 =
          let uu____20108 = elim_delayed_subst_term t in
          (m1, m2, uu____20108) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____20099
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____20116 =
          let uu____20125 = elim_delayed_subst_term t in (d, s, uu____20125) in
        FStar_Syntax_Syntax.Meta_alien uu____20116
    | m -> m
and elim_delayed_subst_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.map
      (fun uu____20148  ->
         match uu____20148 with
         | (t,q) ->
             let uu____20159 = elim_delayed_subst_term t in (uu____20159, q))
      args
and elim_delayed_subst_binders:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    FStar_List.map
      (fun uu____20179  ->
         match uu____20179 with
         | (x,q) ->
             let uu____20190 =
               let uu___173_20191 = x in
               let uu____20192 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___173_20191.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___173_20191.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____20192
               } in
             (uu____20190, q)) bs
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
            | (uu____20268,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____20274,FStar_Util.Inl t) ->
                let uu____20280 =
                  let uu____20283 =
                    let uu____20284 =
                      let uu____20297 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____20297) in
                    FStar_Syntax_Syntax.Tm_arrow uu____20284 in
                  FStar_Syntax_Syntax.mk uu____20283 in
                uu____20280 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____20301 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____20301 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____20329 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____20384 ->
                    let uu____20385 =
                      let uu____20394 =
                        let uu____20395 = FStar_Syntax_Subst.compress t4 in
                        uu____20395.FStar_Syntax_Syntax.n in
                      (uu____20394, tc) in
                    (match uu____20385 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____20420) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____20457) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____20496,FStar_Util.Inl uu____20497) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____20520 -> failwith "Impossible") in
              (match uu____20329 with
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
          let uu____20625 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____20625 with
          | (univ_names1,binders1,tc) ->
              let uu____20683 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20683)
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
          let uu____20718 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20718 with
          | (univ_names1,binders1,tc) ->
              let uu____20778 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20778)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20811 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20811 with
           | (univ_names1,binders1,typ1) ->
               let uu___174_20839 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20839.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20839.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20839.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20839.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___175_20860 = s in
          let uu____20861 =
            let uu____20862 =
              let uu____20871 = FStar_List.map (elim_uvars env) sigs in
              (uu____20871, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20862 in
          {
            FStar_Syntax_Syntax.sigel = uu____20861;
            FStar_Syntax_Syntax.sigrng =
              (uu___175_20860.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___175_20860.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___175_20860.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___175_20860.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20888 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20888 with
           | (univ_names1,uu____20906,typ1) ->
               let uu___176_20920 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___176_20920.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___176_20920.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___176_20920.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___176_20920.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20926 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20926 with
           | (univ_names1,uu____20944,typ1) ->
               let uu___177_20958 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___177_20958.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___177_20958.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___177_20958.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___177_20958.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20992 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20992 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____21015 =
                            let uu____21016 =
                              let uu____21017 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____21017 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____21016 in
                          elim_delayed_subst_term uu____21015 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___178_21020 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___178_21020.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___178_21020.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___179_21021 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___179_21021.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___179_21021.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___179_21021.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___179_21021.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___180_21033 = s in
          let uu____21034 =
            let uu____21035 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____21035 in
          {
            FStar_Syntax_Syntax.sigel = uu____21034;
            FStar_Syntax_Syntax.sigrng =
              (uu___180_21033.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___180_21033.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___180_21033.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___180_21033.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____21039 = elim_uvars_aux_t env us [] t in
          (match uu____21039 with
           | (us1,uu____21057,t1) ->
               let uu___181_21071 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___181_21071.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___181_21071.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___181_21071.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___181_21071.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21072 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21074 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____21074 with
           | (univs1,binders,signature) ->
               let uu____21102 =
                 let uu____21111 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____21111 with
                 | (univs_opening,univs2) ->
                     let uu____21138 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____21138) in
               (match uu____21102 with
                | (univs_opening,univs_closing) ->
                    let uu____21155 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____21161 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____21162 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____21161, uu____21162) in
                    (match uu____21155 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____21184 =
                           match uu____21184 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____21202 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____21202 with
                                | (us1,t1) ->
                                    let uu____21213 =
                                      let uu____21218 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____21225 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____21218, uu____21225) in
                                    (match uu____21213 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____21238 =
                                           let uu____21243 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____21252 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____21243, uu____21252) in
                                         (match uu____21238 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____21268 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____21268 in
                                              let uu____21269 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____21269 with
                                               | (uu____21290,uu____21291,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____21306 =
                                                       let uu____21307 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____21307 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____21306 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____21312 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____21312 with
                           | (uu____21325,uu____21326,t1) -> t1 in
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
                             | uu____21386 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____21403 =
                               let uu____21404 =
                                 FStar_Syntax_Subst.compress body in
                               uu____21404.FStar_Syntax_Syntax.n in
                             match uu____21403 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____21463 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____21492 =
                               let uu____21493 =
                                 FStar_Syntax_Subst.compress t in
                               uu____21493.FStar_Syntax_Syntax.n in
                             match uu____21492 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____21514) ->
                                 let uu____21535 = destruct_action_body body in
                                 (match uu____21535 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____21580 ->
                                 let uu____21581 = destruct_action_body t in
                                 (match uu____21581 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____21630 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____21630 with
                           | (action_univs,t) ->
                               let uu____21639 = destruct_action_typ_templ t in
                               (match uu____21639 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___182_21680 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___182_21680.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___182_21680.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___183_21682 = ed in
                           let uu____21683 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21684 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21685 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21686 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21687 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21688 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21689 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21690 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21691 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21692 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21693 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21694 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21695 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21696 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___183_21682.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___183_21682.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21683;
                             FStar_Syntax_Syntax.bind_wp = uu____21684;
                             FStar_Syntax_Syntax.if_then_else = uu____21685;
                             FStar_Syntax_Syntax.ite_wp = uu____21686;
                             FStar_Syntax_Syntax.stronger = uu____21687;
                             FStar_Syntax_Syntax.close_wp = uu____21688;
                             FStar_Syntax_Syntax.assert_p = uu____21689;
                             FStar_Syntax_Syntax.assume_p = uu____21690;
                             FStar_Syntax_Syntax.null_wp = uu____21691;
                             FStar_Syntax_Syntax.trivial = uu____21692;
                             FStar_Syntax_Syntax.repr = uu____21693;
                             FStar_Syntax_Syntax.return_repr = uu____21694;
                             FStar_Syntax_Syntax.bind_repr = uu____21695;
                             FStar_Syntax_Syntax.actions = uu____21696
                           } in
                         let uu___184_21699 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___184_21699.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___184_21699.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___184_21699.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___184_21699.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___92_21716 =
            match uu___92_21716 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21743 = elim_uvars_aux_t env us [] t in
                (match uu____21743 with
                 | (us1,uu____21767,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___185_21786 = sub_eff in
            let uu____21787 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21790 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___185_21786.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___185_21786.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21787;
              FStar_Syntax_Syntax.lift = uu____21790
            } in
          let uu___186_21793 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___186_21793.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___186_21793.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___186_21793.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___186_21793.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____21803 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21803 with
           | (univ_names1,binders1,comp1) ->
               let uu___187_21837 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___187_21837.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___187_21837.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___187_21837.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___187_21837.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21848 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t