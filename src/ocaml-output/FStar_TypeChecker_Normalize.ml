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
  fun uu___72_517  ->
    match uu___72_517 with
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
  fun uu___73_1397  ->
    match uu___73_1397 with
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
  fun uu___74_1503  ->
    match uu___74_1503 with | [] -> true | uu____1506 -> false
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
                           (let uu___93_2728 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2728.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2728.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2716)) in
                  (match uu____2686 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2744 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2744.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2744.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___95_2893 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2893.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2893.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___96_2894 = lb in
                    let uu____2895 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2894.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2894.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___97_3324 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3324.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3343 = x in
                                let uu____3344 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3343.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3343.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3344
                                } in
                              ((let uu___99_3358 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3358.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3369 = x in
                                let uu____3370 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3369.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3369.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3370
                                } in
                              ((let uu___101_3384 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3384.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3400 = x in
                                let uu____3401 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3400.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3400.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3401
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___103_3408 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3408.FStar_Syntax_Syntax.p)
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
                          let uu___104_3752 = b in
                          let uu____3753 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3752.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3752.FStar_Syntax_Syntax.index);
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
                        (fun uu___75_3900  ->
                           match uu___75_3900 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3904 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3904
                           | f -> f)) in
                 let uu____3908 =
                   let uu___105_3909 = c1 in
                   let uu____3910 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3910;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3909.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___76_3920  ->
            match uu___76_3920 with
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
                   (fun uu___77_3942  ->
                      match uu___77_3942 with
                      | FStar_Syntax_Syntax.DECREASES uu____3943 -> false
                      | uu____3946 -> true)) in
            let rc1 =
              let uu___106_3948 = rc in
              let uu____3949 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3948.FStar_Syntax_Syntax.residual_effect);
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
    let bounded_int_types =
      ["Int8";
      "UInt8";
      "Int16";
      "UInt16";
      "Int32";
      "UInt32";
      "Int64";
      "UInt64";
      "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6145 =
        let uu____6146 =
          let uu____6147 = FStar_Syntax_Syntax.as_arg c in [uu____6147] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6146 in
      uu____6145 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6182 =
              let uu____6195 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6195, (Prims.parse_int "2"),
                (binary_op ()
                   (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                   (fun a486  ->
                      fun a487  ->
                        fun a488  ->
                          (Obj.magic
                             (fun r  ->
                                fun uu____6211  ->
                                  fun uu____6212  ->
                                    match (uu____6211, uu____6212) with
                                    | ((int_to_t1,x),(uu____6231,y)) ->
                                        let uu____6241 =
                                          FStar_BigInt.add_big_int x y in
                                        int_as_bounded r int_to_t1 uu____6241))
                            a486 a487 a488))) in
            let uu____6242 =
              let uu____6257 =
                let uu____6270 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6270, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                     (fun a490  ->
                        fun a491  ->
                          fun a492  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6286  ->
                                    fun uu____6287  ->
                                      match (uu____6286, uu____6287) with
                                      | ((int_to_t1,x),(uu____6306,y)) ->
                                          let uu____6316 =
                                            FStar_BigInt.sub_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6316)) a490 a491 a492))) in
              let uu____6317 =
                let uu____6332 =
                  let uu____6345 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6345, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                       (fun a494  ->
                          fun a495  ->
                            fun a496  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6361  ->
                                      fun uu____6362  ->
                                        match (uu____6361, uu____6362) with
                                        | ((int_to_t1,x),(uu____6381,y)) ->
                                            let uu____6391 =
                                              FStar_BigInt.mult_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6391)) a494 a495 a496))) in
                [uu____6332] in
              uu____6257 :: uu____6317 in
            uu____6182 :: uu____6242)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6481)::(a1,uu____6483)::(a2,uu____6485)::[] ->
        let uu____6522 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6522 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6528 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6528.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6528.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6532 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6532.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6532.FStar_Syntax_Syntax.vars)
                })
         | uu____6533 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6535)::uu____6536::(a1,uu____6538)::(a2,uu____6540)::[] ->
        let uu____6589 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6589 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6595 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6595.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6595.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6599 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6599.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6599.FStar_Syntax_Syntax.vars)
                })
         | uu____6600 -> FStar_Pervasives_Native.None)
    | uu____6601 -> failwith "Unexpected number of arguments" in
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
      let uu____6620 =
        let uu____6621 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6621 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6620
    with | uu____6627 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6631 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6631) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6691  ->
           fun subst1  ->
             match uu____6691 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6732,uu____6733)) ->
                      let uu____6792 = b in
                      (match uu____6792 with
                       | (bv,uu____6800) ->
                           let uu____6801 =
                             let uu____6802 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6802 in
                           if uu____6801
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6807 = unembed_binder term1 in
                              match uu____6807 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6814 =
                                      let uu___111_6815 = bv in
                                      let uu____6816 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_6815.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_6815.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6816
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6814 in
                                  let b_for_x =
                                    let uu____6820 =
                                      let uu____6827 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6827) in
                                    FStar_Syntax_Syntax.NT uu____6820 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_6836  ->
                                         match uu___78_6836 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6837,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6839;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6840;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6845 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6846 -> subst1)) env []
let reduce_primops:
  'Auu____6863 'Auu____6864 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6864) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6863 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6905 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6905
          then tm
          else
            (let uu____6907 = FStar_Syntax_Util.head_and_args tm in
             match uu____6907 with
             | (head1,args) ->
                 let uu____6944 =
                   let uu____6945 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6945.FStar_Syntax_Syntax.n in
                 (match uu____6944 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6949 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6949 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6966  ->
                                   let uu____6967 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6968 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6975 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6967 uu____6968 uu____6975);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6980  ->
                                   let uu____6981 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6981);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6984  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6986 =
                                 prim_step.interpretation psc args in
                               match uu____6986 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6992  ->
                                         let uu____6993 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6993);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6999  ->
                                         let uu____7000 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7001 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7000 uu____7001);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7002 ->
                           (log_primops cfg
                              (fun uu____7006  ->
                                 let uu____7007 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7007);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7011  ->
                            let uu____7012 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7012);
                       (match args with
                        | (a1,uu____7014)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7031 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7043  ->
                            let uu____7044 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7044);
                       (match args with
                        | (t,uu____7046)::(r,uu____7048)::[] ->
                            let uu____7075 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7075 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7079 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7079.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7079.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7082 -> tm))
                  | uu____7091 -> tm))
let reduce_equality:
  'Auu____7096 'Auu____7097 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7097) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7096 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7135 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___113_7135.tcenv);
           delta_level = (uu___113_7135.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7135.strong);
           memoize_lazy = (uu___113_7135.memoize_lazy);
           normalize_pure_lets = (uu___113_7135.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____7142 'Auu____7143 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7143) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7142 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7185 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7185
          then tm1
          else
            (let w t =
               let uu___114_7197 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7197.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7197.FStar_Syntax_Syntax.vars)
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
               | uu____7214 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7219 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7219
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7240 =
                 match uu____7240 with
                 | (t1,q) ->
                     let uu____7253 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7253 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7281 -> (t1, q)) in
               let uu____7290 = FStar_Syntax_Util.head_and_args t in
               match uu____7290 with
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
                         FStar_Syntax_Syntax.pos = uu____7387;
                         FStar_Syntax_Syntax.vars = uu____7388;_},uu____7389);
                    FStar_Syntax_Syntax.pos = uu____7390;
                    FStar_Syntax_Syntax.vars = uu____7391;_},args)
                 ->
                 let uu____7417 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7417
                 then
                   let uu____7418 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7418 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7473)::
                        (uu____7474,(arg,uu____7476))::[] ->
                        maybe_auto_squash arg
                    | (uu____7541,(arg,uu____7543))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7544)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7609)::uu____7610::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7673::(FStar_Pervasives_Native.Some (false
                                   ),uu____7674)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7737 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7753 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7753
                    then
                      let uu____7754 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7754 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7809)::uu____7810::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7873::(FStar_Pervasives_Native.Some (true
                                     ),uu____7874)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7937)::
                          (uu____7938,(arg,uu____7940))::[] ->
                          maybe_auto_squash arg
                      | (uu____8005,(arg,uu____8007))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8008)::[]
                          -> maybe_auto_squash arg
                      | uu____8073 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8089 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8089
                       then
                         let uu____8090 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8090 with
                         | uu____8145::(FStar_Pervasives_Native.Some (true
                                        ),uu____8146)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8209)::uu____8210::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8273)::
                             (uu____8274,(arg,uu____8276))::[] ->
                             maybe_auto_squash arg
                         | (uu____8341,(p,uu____8343))::(uu____8344,(q,uu____8346))::[]
                             ->
                             let uu____8411 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8411
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8413 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8429 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8429
                          then
                            let uu____8430 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8430 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8485)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8524)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8563 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8579 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8579
                             then
                               match args with
                               | (t,uu____8581)::[] ->
                                   let uu____8598 =
                                     let uu____8599 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8599.FStar_Syntax_Syntax.n in
                                   (match uu____8598 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8602::[],body,uu____8604) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8631 -> tm1)
                                    | uu____8634 -> tm1)
                               | (uu____8635,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8636))::
                                   (t,uu____8638)::[] ->
                                   let uu____8677 =
                                     let uu____8678 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8678.FStar_Syntax_Syntax.n in
                                   (match uu____8677 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8681::[],body,uu____8683) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8710 -> tm1)
                                    | uu____8713 -> tm1)
                               | uu____8714 -> tm1
                             else
                               (let uu____8724 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8724
                                then
                                  match args with
                                  | (t,uu____8726)::[] ->
                                      let uu____8743 =
                                        let uu____8744 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8744.FStar_Syntax_Syntax.n in
                                      (match uu____8743 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8747::[],body,uu____8749)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8776 -> tm1)
                                       | uu____8779 -> tm1)
                                  | (uu____8780,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8781))::(t,uu____8783)::[] ->
                                      let uu____8822 =
                                        let uu____8823 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8823.FStar_Syntax_Syntax.n in
                                      (match uu____8822 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8826::[],body,uu____8828)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8855 -> tm1)
                                       | uu____8858 -> tm1)
                                  | uu____8859 -> tm1
                                else
                                  (let uu____8869 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8869
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8870;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8871;_},uu____8872)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8889;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8890;_},uu____8891)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8908 -> tm1
                                   else
                                     (let uu____8918 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8918 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8938 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8948;
                    FStar_Syntax_Syntax.vars = uu____8949;_},args)
                 ->
                 let uu____8971 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8971
                 then
                   let uu____8972 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8972 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9027)::
                        (uu____9028,(arg,uu____9030))::[] ->
                        maybe_auto_squash arg
                    | (uu____9095,(arg,uu____9097))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9098)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9163)::uu____9164::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9227::(FStar_Pervasives_Native.Some (false
                                   ),uu____9228)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9291 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9307 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9307
                    then
                      let uu____9308 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9308 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9363)::uu____9364::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9427::(FStar_Pervasives_Native.Some (true
                                     ),uu____9428)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9491)::
                          (uu____9492,(arg,uu____9494))::[] ->
                          maybe_auto_squash arg
                      | (uu____9559,(arg,uu____9561))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9562)::[]
                          -> maybe_auto_squash arg
                      | uu____9627 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9643 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9643
                       then
                         let uu____9644 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9644 with
                         | uu____9699::(FStar_Pervasives_Native.Some (true
                                        ),uu____9700)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9763)::uu____9764::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9827)::
                             (uu____9828,(arg,uu____9830))::[] ->
                             maybe_auto_squash arg
                         | (uu____9895,(p,uu____9897))::(uu____9898,(q,uu____9900))::[]
                             ->
                             let uu____9965 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9965
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9967 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9983 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9983
                          then
                            let uu____9984 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9984 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10039)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10078)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10117 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10133 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10133
                             then
                               match args with
                               | (t,uu____10135)::[] ->
                                   let uu____10152 =
                                     let uu____10153 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10153.FStar_Syntax_Syntax.n in
                                   (match uu____10152 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10156::[],body,uu____10158) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10185 -> tm1)
                                    | uu____10188 -> tm1)
                               | (uu____10189,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10190))::
                                   (t,uu____10192)::[] ->
                                   let uu____10231 =
                                     let uu____10232 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10232.FStar_Syntax_Syntax.n in
                                   (match uu____10231 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10235::[],body,uu____10237) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10264 -> tm1)
                                    | uu____10267 -> tm1)
                               | uu____10268 -> tm1
                             else
                               (let uu____10278 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10278
                                then
                                  match args with
                                  | (t,uu____10280)::[] ->
                                      let uu____10297 =
                                        let uu____10298 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10298.FStar_Syntax_Syntax.n in
                                      (match uu____10297 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10301::[],body,uu____10303)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10330 -> tm1)
                                       | uu____10333 -> tm1)
                                  | (uu____10334,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10335))::(t,uu____10337)::[] ->
                                      let uu____10376 =
                                        let uu____10377 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10377.FStar_Syntax_Syntax.n in
                                      (match uu____10376 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10380::[],body,uu____10382)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10409 -> tm1)
                                       | uu____10412 -> tm1)
                                  | uu____10413 -> tm1
                                else
                                  (let uu____10423 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10423
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10424;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10425;_},uu____10426)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10443;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10444;_},uu____10445)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10462 -> tm1
                                   else
                                     (let uu____10472 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10472 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10492 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10501 -> tm1)
let maybe_simplify:
  'Auu____10508 'Auu____10509 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10509) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10508 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10552 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10552
           then
             let uu____10553 = FStar_Syntax_Print.term_to_string tm in
             let uu____10554 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10553 uu____10554
           else ());
          tm'
let is_norm_request:
  'Auu____10560 .
    FStar_Syntax_Syntax.term -> 'Auu____10560 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10573 =
        let uu____10580 =
          let uu____10581 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10581.FStar_Syntax_Syntax.n in
        (uu____10580, args) in
      match uu____10573 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10587::uu____10588::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10592::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10597::uu____10598::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10601 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___79_10612  ->
    match uu___79_10612 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10618 =
          let uu____10621 =
            let uu____10622 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10622 in
          [uu____10621] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10618
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10638 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10638) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10676 =
          let uu____10679 =
            let uu____10684 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10684 s in
          FStar_All.pipe_right uu____10679 FStar_Util.must in
        FStar_All.pipe_right uu____10676 tr_norm_steps in
      match args with
      | uu____10709::(tm,uu____10711)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10734)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10749)::uu____10750::(tm,uu____10752)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10792 =
              let uu____10795 = full_norm steps in parse_steps uu____10795 in
            Beta :: uu____10792 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10804 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___80_10821  ->
    match uu___80_10821 with
    | (App
        (uu____10824,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10825;
                       FStar_Syntax_Syntax.vars = uu____10826;_},uu____10827,uu____10828))::uu____10829
        -> true
    | uu____10836 -> false
let firstn:
  'Auu____10842 .
    Prims.int ->
      'Auu____10842 Prims.list ->
        ('Auu____10842 Prims.list,'Auu____10842 Prims.list)
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
          (uu____10878,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10879;
                         FStar_Syntax_Syntax.vars = uu____10880;_},uu____10881,uu____10882))::uu____10883
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10890 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11037  ->
               let uu____11038 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11039 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11040 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11047 =
                 let uu____11048 =
                   let uu____11051 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11051 in
                 stack_to_string uu____11048 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11038 uu____11039 uu____11040 uu____11047);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11074 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11099 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11116 =
                 let uu____11117 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11118 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11117 uu____11118 in
               failwith uu____11116
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11119 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11136 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11137 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11138;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11139;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11142;
                 FStar_Syntax_Syntax.fv_delta = uu____11143;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11144;
                 FStar_Syntax_Syntax.fv_delta = uu____11145;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11146);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11154 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11154 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11160  ->
                     let uu____11161 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11162 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11161 uu____11162);
                if b
                then
                  (let uu____11163 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11163 t1 fv)
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
                 let uu___115_11202 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11202.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11202.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11235 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11235) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11243 = cfg in
                 let uu____11244 =
                   FStar_List.filter
                     (fun uu___81_11247  ->
                        match uu___81_11247 with
                        | UnfoldOnly uu____11248 -> false
                        | NoDeltaSteps  -> false
                        | uu____11251 -> true) cfg.steps in
                 {
                   steps = uu____11244;
                   tcenv = (uu___116_11243.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11243.primitive_steps);
                   strong = (uu___116_11243.strong);
                   memoize_lazy = (uu___116_11243.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____11252 = get_norm_request (norm cfg' env []) args in
               (match uu____11252 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11268 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11273  ->
                                match uu___82_11273 with
                                | UnfoldUntil uu____11274 -> true
                                | UnfoldOnly uu____11275 -> true
                                | uu____11278 -> false)) in
                      if uu____11268
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___117_11283 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___117_11283.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11283.primitive_steps);
                        strong = (uu___117_11283.strong);
                        memoize_lazy = (uu___117_11283.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11290 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11290
                      then
                        let uu____11293 =
                          let uu____11294 =
                            let uu____11299 = FStar_Util.now () in
                            (t1, uu____11299) in
                          Debug uu____11294 in
                        uu____11293 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11303 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11303
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11310 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11310
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11313 =
                      let uu____11320 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11320, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11313 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11333  ->
                         match uu___83_11333 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11336 =
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
                 if uu____11336
                 then false
                 else
                   (let uu____11338 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11345  ->
                              match uu___84_11345 with
                              | UnfoldOnly uu____11346 -> true
                              | UnfoldAttr uu____11349 -> true
                              | uu____11350 -> false)) in
                    match uu____11338 with
                    | FStar_Pervasives_Native.Some uu____11351 ->
                        let attr_eq a a' =
                          let uu____11359 = FStar_Syntax_Util.eq_tm a a' in
                          match uu____11359 with
                          | FStar_Syntax_Util.Equal  -> true
                          | uu____11360 -> false in
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
                                      let uu____11370 =
                                        FStar_TypeChecker_Env.lookup_attrs_of_lid
                                          cfg.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      (match uu____11370 with
                                       | FStar_Pervasives_Native.Some attrs
                                           ->
                                           acc ||
                                             (FStar_Util.for_some
                                                (attr_eq attr) attrs)
                                       | uu____11380 -> acc)
                                  | uu____11385 -> acc) false cfg.steps)
                    | uu____11386 -> should_delta) in
               (log cfg
                  (fun uu____11394  ->
                     let uu____11395 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11396 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11397 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11395 uu____11396 uu____11397);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11400 = lookup_bvar env x in
               (match uu____11400 with
                | Univ uu____11403 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11452 = FStar_ST.op_Bang r in
                      (match uu____11452 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11570  ->
                                 let uu____11571 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11572 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11571
                                   uu____11572);
                            (let uu____11573 =
                               let uu____11574 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11574.FStar_Syntax_Syntax.n in
                             match uu____11573 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11577 ->
                                 norm cfg env2 stack t'
                             | uu____11594 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11664)::uu____11665 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11674)::uu____11675 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11685,uu____11686))::stack_rest ->
                    (match c with
                     | Univ uu____11690 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11699 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11720  ->
                                    let uu____11721 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11721);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11761  ->
                                    let uu____11762 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11762);
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
                       (fun uu____11840  ->
                          let uu____11841 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11841);
                     norm cfg env stack1 t1)
                | (Debug uu____11842)::uu____11843 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11850 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11850
                    else
                      (let uu____11852 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11852 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11894  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11922 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11922
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11932 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11932)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11937 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11937.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11937.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11938 -> lopt in
                           (log cfg
                              (fun uu____11944  ->
                                 let uu____11945 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11945);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_11954 = cfg in
                               {
                                 steps = (uu___119_11954.steps);
                                 tcenv = (uu___119_11954.tcenv);
                                 delta_level = (uu___119_11954.delta_level);
                                 primitive_steps =
                                   (uu___119_11954.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_11954.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_11954.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11965)::uu____11966 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11973 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11973
                    else
                      (let uu____11975 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11975 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12017  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12045 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12045
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12055 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12055)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12060 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12060.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12060.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12061 -> lopt in
                           (log cfg
                              (fun uu____12067  ->
                                 let uu____12068 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12068);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12077 = cfg in
                               {
                                 steps = (uu___119_12077.steps);
                                 tcenv = (uu___119_12077.tcenv);
                                 delta_level = (uu___119_12077.delta_level);
                                 primitive_steps =
                                   (uu___119_12077.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12077.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12077.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12088)::uu____12089 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12100 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12100
                    else
                      (let uu____12102 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12102 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12144  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12172 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12172
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12182 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12182)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12187 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12187.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12187.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12188 -> lopt in
                           (log cfg
                              (fun uu____12194  ->
                                 let uu____12195 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12195);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12204 = cfg in
                               {
                                 steps = (uu___119_12204.steps);
                                 tcenv = (uu___119_12204.tcenv);
                                 delta_level = (uu___119_12204.delta_level);
                                 primitive_steps =
                                   (uu___119_12204.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12204.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12204.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12215)::uu____12216 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12227 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12227
                    else
                      (let uu____12229 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12229 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12271  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12299 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12299
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12309 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12309)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12314 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12314.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12314.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12315 -> lopt in
                           (log cfg
                              (fun uu____12321  ->
                                 let uu____12322 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12322);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12331 = cfg in
                               {
                                 steps = (uu___119_12331.steps);
                                 tcenv = (uu___119_12331.tcenv);
                                 delta_level = (uu___119_12331.delta_level);
                                 primitive_steps =
                                   (uu___119_12331.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12331.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12331.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12342)::uu____12343 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12358 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12358
                    else
                      (let uu____12360 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12360 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12402  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12430 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12430
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12440 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12440)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12445 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12445.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12445.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12446 -> lopt in
                           (log cfg
                              (fun uu____12452  ->
                                 let uu____12453 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12453);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12462 = cfg in
                               {
                                 steps = (uu___119_12462.steps);
                                 tcenv = (uu___119_12462.tcenv);
                                 delta_level = (uu___119_12462.delta_level);
                                 primitive_steps =
                                   (uu___119_12462.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12462.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12462.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12473 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12473
                    else
                      (let uu____12475 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12475 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12517  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12545 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12545
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12555 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12555)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12560 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12560.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12560.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12561 -> lopt in
                           (log cfg
                              (fun uu____12567  ->
                                 let uu____12568 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12568);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12577 = cfg in
                               {
                                 steps = (uu___119_12577.steps);
                                 tcenv = (uu___119_12577.tcenv);
                                 delta_level = (uu___119_12577.delta_level);
                                 primitive_steps =
                                   (uu___119_12577.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12577.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12577.normalize_pure_lets)
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
                      (fun uu____12626  ->
                         fun stack1  ->
                           match uu____12626 with
                           | (a,aq) ->
                               let uu____12638 =
                                 let uu____12639 =
                                   let uu____12646 =
                                     let uu____12647 =
                                       let uu____12678 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12678, false) in
                                     Clos uu____12647 in
                                   (uu____12646, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12639 in
                               uu____12638 :: stack1) args) in
               (log cfg
                  (fun uu____12762  ->
                     let uu____12763 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12763);
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
                             ((let uu___120_12799 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_12799.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_12799.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12800 ->
                      let uu____12805 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12805)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12808 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12808 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12839 =
                          let uu____12840 =
                            let uu____12847 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_12849 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_12849.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_12849.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12847) in
                          FStar_Syntax_Syntax.Tm_refine uu____12840 in
                        mk uu____12839 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12868 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12868
               else
                 (let uu____12870 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12870 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12878 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12902  -> dummy :: env1) env) in
                        norm_comp cfg uu____12878 c1 in
                      let t2 =
                        let uu____12924 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12924 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12983)::uu____12984 ->
                    (log cfg
                       (fun uu____12995  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12996)::uu____12997 ->
                    (log cfg
                       (fun uu____13008  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13009,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13010;
                                   FStar_Syntax_Syntax.vars = uu____13011;_},uu____13012,uu____13013))::uu____13014
                    ->
                    (log cfg
                       (fun uu____13023  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13024)::uu____13025 ->
                    (log cfg
                       (fun uu____13036  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13037 ->
                    (log cfg
                       (fun uu____13040  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13044  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13061 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13061
                         | FStar_Util.Inr c ->
                             let uu____13069 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13069 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13082 =
                               let uu____13083 =
                                 let uu____13110 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13110, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13083 in
                             mk uu____13082 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13129 ->
                           let uu____13130 =
                             let uu____13131 =
                               let uu____13132 =
                                 let uu____13159 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13159, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13132 in
                             mk uu____13131 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13130))))
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
                         let uu____13269 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13269 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13289 = cfg in
                               let uu____13290 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___122_13289.steps);
                                 tcenv = uu____13290;
                                 delta_level = (uu___122_13289.delta_level);
                                 primitive_steps =
                                   (uu___122_13289.primitive_steps);
                                 strong = (uu___122_13289.strong);
                                 memoize_lazy = (uu___122_13289.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___122_13289.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____13295 =
                                 let uu____13296 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13296 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13295 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___123_13299 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13299.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13299.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13300 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13300
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13311,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13312;
                               FStar_Syntax_Syntax.lbunivs = uu____13313;
                               FStar_Syntax_Syntax.lbtyp = uu____13314;
                               FStar_Syntax_Syntax.lbeff = uu____13315;
                               FStar_Syntax_Syntax.lbdef = uu____13316;_}::uu____13317),uu____13318)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13354 =
                 (let uu____13357 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13357) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13359 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13359))) in
               if uu____13354
               then
                 let binder =
                   let uu____13361 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13361 in
                 let env1 =
                   let uu____13371 =
                     let uu____13378 =
                       let uu____13379 =
                         let uu____13410 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13410,
                           false) in
                       Clos uu____13379 in
                     ((FStar_Pervasives_Native.Some binder), uu____13378) in
                   uu____13371 :: env in
                 (log cfg
                    (fun uu____13503  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13505 =
                    let uu____13510 =
                      let uu____13511 =
                        let uu____13512 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13512
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13511] in
                    FStar_Syntax_Subst.open_term uu____13510 body in
                  match uu____13505 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13521  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13529 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13529 in
                          FStar_Util.Inl
                            (let uu___124_13539 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13539.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13539.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13542  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13544 = lb in
                           let uu____13545 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13544.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13544.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13545
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13580  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___126_13603 = cfg in
                           {
                             steps = (uu___126_13603.steps);
                             tcenv = (uu___126_13603.tcenv);
                             delta_level = (uu___126_13603.delta_level);
                             primitive_steps =
                               (uu___126_13603.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13603.memoize_lazy);
                             normalize_pure_lets =
                               (uu___126_13603.normalize_pure_lets)
                           } in
                         log cfg1
                           (fun uu____13606  ->
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
               let uu____13623 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13623 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13659 =
                               let uu___127_13660 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13660.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13660.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13659 in
                           let uu____13661 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13661 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13687 =
                                   FStar_List.map (fun uu____13703  -> dummy)
                                     lbs1 in
                                 let uu____13704 =
                                   let uu____13713 =
                                     FStar_List.map
                                       (fun uu____13733  -> dummy) xs1 in
                                   FStar_List.append uu____13713 env in
                                 FStar_List.append uu____13687 uu____13704 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13757 =
                                       let uu___128_13758 = rc in
                                       let uu____13759 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13758.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13759;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13758.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13757
                                 | uu____13766 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___129_13770 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_13770.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_13770.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13780 =
                        FStar_List.map (fun uu____13796  -> dummy) lbs2 in
                      FStar_List.append uu____13780 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13804 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13804 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_13820 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_13820.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_13820.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13847 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13847
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13866 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13942  ->
                        match uu____13942 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14063 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14063.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14063.FStar_Syntax_Syntax.sort)
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
               (match uu____13866 with
                | (rec_env,memos,uu____14276) ->
                    let uu____14329 =
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
                             let uu____14640 =
                               let uu____14647 =
                                 let uu____14648 =
                                   let uu____14679 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14679, false) in
                                 Clos uu____14648 in
                               (FStar_Pervasives_Native.None, uu____14647) in
                             uu____14640 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14789  ->
                     let uu____14790 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14790);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14812 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14814::uu____14815 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14820) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14821 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14852 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14866 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14866
                              | uu____14877 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2))))
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
              let uu____14889 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14889 in
            let uu____14890 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14890 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14903  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14914  ->
                      let uu____14915 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14916 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14915
                        uu____14916);
                 (let t1 =
                    let uu____14918 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14920 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____14920) in
                    if uu____14918
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
                    | (UnivArgs (us',uu____14930))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____14985 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____14988 ->
                        let uu____14991 =
                          let uu____14992 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14992 in
                        failwith uu____14991
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
                let uu____15013 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15013
                then
                  let uu___132_15014 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_15014.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_15014.primitive_steps);
                    strong = (uu___132_15014.strong);
                    memoize_lazy = (uu___132_15014.memoize_lazy);
                    normalize_pure_lets =
                      (uu___132_15014.normalize_pure_lets)
                  }
                else
                  (let uu___133_15016 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_15016.tcenv);
                     delta_level = (uu___133_15016.delta_level);
                     primitive_steps = (uu___133_15016.primitive_steps);
                     strong = (uu___133_15016.strong);
                     memoize_lazy = (uu___133_15016.memoize_lazy);
                     normalize_pure_lets =
                       (uu___133_15016.normalize_pure_lets)
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
                  (fun uu____15045  ->
                     let uu____15046 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15047 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15046
                       uu____15047);
                (let uu____15048 =
                   let uu____15049 = FStar_Syntax_Subst.compress head2 in
                   uu____15049.FStar_Syntax_Syntax.n in
                 match uu____15048 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15067 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15067 with
                      | (uu____15068,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15074 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15082 =
                                   let uu____15083 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15083.FStar_Syntax_Syntax.n in
                                 match uu____15082 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15089,uu____15090))
                                     ->
                                     let uu____15099 =
                                       let uu____15100 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15100.FStar_Syntax_Syntax.n in
                                     (match uu____15099 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15106,msrc,uu____15108))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15117 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15117
                                      | uu____15118 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15119 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15120 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15120 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15125 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15125.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15125.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15125.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15126 = FStar_List.tl stack in
                                    let uu____15127 =
                                      let uu____15128 =
                                        let uu____15131 =
                                          let uu____15132 =
                                            let uu____15145 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15145) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15132 in
                                        FStar_Syntax_Syntax.mk uu____15131 in
                                      uu____15128
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15126 uu____15127
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15161 =
                                      let uu____15162 = is_return body in
                                      match uu____15162 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15166;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15167;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15172 -> false in
                                    if uu____15161
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
                                         let uu____15195 =
                                           let uu____15198 =
                                             let uu____15199 =
                                               let uu____15216 =
                                                 let uu____15219 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15219] in
                                               (uu____15216, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15199 in
                                           FStar_Syntax_Syntax.mk uu____15198 in
                                         uu____15195
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15235 =
                                           let uu____15236 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15236.FStar_Syntax_Syntax.n in
                                         match uu____15235 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15242::uu____15243::[])
                                             ->
                                             let uu____15250 =
                                               let uu____15253 =
                                                 let uu____15254 =
                                                   let uu____15261 =
                                                     let uu____15264 =
                                                       let uu____15265 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15265 in
                                                     let uu____15266 =
                                                       let uu____15269 =
                                                         let uu____15270 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15270 in
                                                       [uu____15269] in
                                                     uu____15264 ::
                                                       uu____15266 in
                                                   (bind1, uu____15261) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15254 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15253 in
                                             uu____15250
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15278 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15284 =
                                           let uu____15287 =
                                             let uu____15288 =
                                               let uu____15303 =
                                                 let uu____15306 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15307 =
                                                   let uu____15310 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15311 =
                                                     let uu____15314 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15315 =
                                                       let uu____15318 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15319 =
                                                         let uu____15322 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15323 =
                                                           let uu____15326 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15326] in
                                                         uu____15322 ::
                                                           uu____15323 in
                                                       uu____15318 ::
                                                         uu____15319 in
                                                     uu____15314 ::
                                                       uu____15315 in
                                                   uu____15310 :: uu____15311 in
                                                 uu____15306 :: uu____15307 in
                                               (bind_inst, uu____15303) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15288 in
                                           FStar_Syntax_Syntax.mk uu____15287 in
                                         uu____15284
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15337  ->
                                            let uu____15338 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15338);
                                       (let uu____15339 = FStar_List.tl stack in
                                        norm cfg env uu____15339 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15363 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15363 with
                      | (uu____15364,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15399 =
                                  let uu____15400 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15400.FStar_Syntax_Syntax.n in
                                match uu____15399 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15406) -> t2
                                | uu____15411 -> head3 in
                              let uu____15412 =
                                let uu____15413 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15413.FStar_Syntax_Syntax.n in
                              match uu____15412 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15419 -> FStar_Pervasives_Native.None in
                            let uu____15420 = maybe_extract_fv head3 in
                            match uu____15420 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15430 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15430
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15435 = maybe_extract_fv head4 in
                                  match uu____15435 with
                                  | FStar_Pervasives_Native.Some uu____15440
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15441 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15446 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15461 =
                              match uu____15461 with
                              | (e,q) ->
                                  let uu____15468 =
                                    let uu____15469 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15469.FStar_Syntax_Syntax.n in
                                  (match uu____15468 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15484 -> false) in
                            let uu____15485 =
                              let uu____15486 =
                                let uu____15493 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15493 :: args in
                              FStar_Util.for_some is_arg_impure uu____15486 in
                            if uu____15485
                            then
                              let uu____15498 =
                                let uu____15499 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15499 in
                              failwith uu____15498
                            else ());
                           (let uu____15501 = maybe_unfold_action head_app in
                            match uu____15501 with
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
                                let uu____15538 = FStar_List.tl stack in
                                norm cfg env uu____15538 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15540) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15564 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15564 in
                     (log cfg
                        (fun uu____15568  ->
                           let uu____15569 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15569);
                      (let uu____15570 = FStar_List.tl stack in
                       norm cfg env uu____15570 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15572) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15697  ->
                               match uu____15697 with
                               | (pat,wopt,tm) ->
                                   let uu____15745 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15745))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15777 = FStar_List.tl stack in
                     norm cfg env uu____15777 tm
                 | uu____15778 -> fallback ())
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
              (fun uu____15792  ->
                 let uu____15793 = FStar_Ident.string_of_lid msrc in
                 let uu____15794 = FStar_Ident.string_of_lid mtgt in
                 let uu____15795 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15793
                   uu____15794 uu____15795);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15797 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15797 with
               | (uu____15798,return_repr) ->
                   let return_inst =
                     let uu____15807 =
                       let uu____15808 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15808.FStar_Syntax_Syntax.n in
                     match uu____15807 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15814::[]) ->
                         let uu____15821 =
                           let uu____15824 =
                             let uu____15825 =
                               let uu____15832 =
                                 let uu____15835 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15835] in
                               (return_tm, uu____15832) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15825 in
                           FStar_Syntax_Syntax.mk uu____15824 in
                         uu____15821 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15843 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15846 =
                     let uu____15849 =
                       let uu____15850 =
                         let uu____15865 =
                           let uu____15868 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15869 =
                             let uu____15872 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15872] in
                           uu____15868 :: uu____15869 in
                         (return_inst, uu____15865) in
                       FStar_Syntax_Syntax.Tm_app uu____15850 in
                     FStar_Syntax_Syntax.mk uu____15849 in
                   uu____15846 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15881 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15881 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15884 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15884
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15885;
                     FStar_TypeChecker_Env.mtarget = uu____15886;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15887;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15902;
                     FStar_TypeChecker_Env.mtarget = uu____15903;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15904;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15928 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____15929 = FStar_Syntax_Util.mk_reify e in
                   lift uu____15928 t FStar_Syntax_Syntax.tun uu____15929)
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
                (fun uu____15985  ->
                   match uu____15985 with
                   | (a,imp) ->
                       let uu____15996 = norm cfg env [] a in
                       (uu____15996, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_16010 = comp in
            let uu____16011 =
              let uu____16012 =
                let uu____16021 = norm cfg env [] t in
                let uu____16022 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16021, uu____16022) in
              FStar_Syntax_Syntax.Total uu____16012 in
            {
              FStar_Syntax_Syntax.n = uu____16011;
              FStar_Syntax_Syntax.pos =
                (uu___135_16010.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16010.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_16037 = comp in
            let uu____16038 =
              let uu____16039 =
                let uu____16048 = norm cfg env [] t in
                let uu____16049 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16048, uu____16049) in
              FStar_Syntax_Syntax.GTotal uu____16039 in
            {
              FStar_Syntax_Syntax.n = uu____16038;
              FStar_Syntax_Syntax.pos =
                (uu___136_16037.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16037.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16101  ->
                      match uu____16101 with
                      | (a,i) ->
                          let uu____16112 = norm cfg env [] a in
                          (uu____16112, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16123  ->
                      match uu___85_16123 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16127 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16127
                      | f -> f)) in
            let uu___137_16131 = comp in
            let uu____16132 =
              let uu____16133 =
                let uu___138_16134 = ct in
                let uu____16135 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16136 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16139 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16135;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16134.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16136;
                  FStar_Syntax_Syntax.effect_args = uu____16139;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16133 in
            {
              FStar_Syntax_Syntax.n = uu____16132;
              FStar_Syntax_Syntax.pos =
                (uu___137_16131.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16131.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16150  ->
        match uu____16150 with
        | (x,imp) ->
            let uu____16153 =
              let uu___139_16154 = x in
              let uu____16155 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16154.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16154.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16155
              } in
            (uu____16153, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16161 =
          FStar_List.fold_left
            (fun uu____16179  ->
               fun b  ->
                 match uu____16179 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16161 with | (nbs,uu____16219) -> FStar_List.rev nbs
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
            let uu____16235 =
              let uu___140_16236 = rc in
              let uu____16237 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16236.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16237;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16236.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16235
        | uu____16244 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16257  ->
               let uu____16258 = FStar_Syntax_Print.tag_of_term t in
               let uu____16259 = FStar_Syntax_Print.term_to_string t in
               let uu____16260 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16267 =
                 let uu____16268 =
                   let uu____16271 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16271 in
                 stack_to_string uu____16268 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16258 uu____16259 uu____16260 uu____16267);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16300 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16300
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16302 =
                     let uu____16303 =
                       let uu____16304 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16304 in
                     FStar_Util.string_of_int uu____16303 in
                   let uu____16309 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16310 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16302 uu____16309 uu____16310
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16364  ->
                     let uu____16365 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16365);
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
               let uu____16401 =
                 let uu___141_16402 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16402.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16402.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16401
           | (Arg (Univ uu____16403,uu____16404,uu____16405))::uu____16406 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16409,uu____16410))::uu____16411 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16427),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16480  ->
                     let uu____16481 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16481);
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
                  (let uu____16491 = FStar_ST.op_Bang m in
                   match uu____16491 with
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
                   | FStar_Pervasives_Native.Some (uu____16628,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16675 =
                 log cfg
                   (fun uu____16679  ->
                      let uu____16680 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16680);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16684 =
                 let uu____16685 = FStar_Syntax_Subst.compress t in
                 uu____16685.FStar_Syntax_Syntax.n in
               (match uu____16684 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16712 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16712 in
                    (log cfg
                       (fun uu____16716  ->
                          let uu____16717 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16717);
                     (let uu____16718 = FStar_List.tl stack in
                      norm cfg env1 uu____16718 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16719);
                       FStar_Syntax_Syntax.pos = uu____16720;
                       FStar_Syntax_Syntax.vars = uu____16721;_},(e,uu____16723)::[])
                    -> norm cfg env1 stack' e
                | uu____16752 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16763 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16763
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16775  ->
                     let uu____16776 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16776);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16781 =
                   log cfg
                     (fun uu____16786  ->
                        let uu____16787 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16788 =
                          let uu____16789 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16806  ->
                                    match uu____16806 with
                                    | (p,uu____16816,uu____16817) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16789
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16787 uu____16788);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_16834  ->
                                match uu___86_16834 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16835 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___142_16839 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_16839.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_16839.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_16839.memoize_lazy);
                        normalize_pure_lets =
                          (uu___142_16839.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16871 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16892 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16952  ->
                                    fun uu____16953  ->
                                      match (uu____16952, uu____16953) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17044 = norm_pat env3 p1 in
                                          (match uu____17044 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16892 with
                           | (pats1,env3) ->
                               ((let uu___143_17126 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17126.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17145 = x in
                            let uu____17146 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17145.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17145.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17146
                            } in
                          ((let uu___145_17160 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17160.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17171 = x in
                            let uu____17172 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17171.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17171.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17172
                            } in
                          ((let uu___147_17186 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17186.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___148_17202 = x in
                            let uu____17203 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17202.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17202.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17203
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___149_17210 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17210.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17220 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17234 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17234 with
                                  | (p,wopt,e) ->
                                      let uu____17254 = norm_pat env1 p in
                                      (match uu____17254 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17279 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17279 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17285 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17285) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17295) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17300 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17301;
                         FStar_Syntax_Syntax.fv_delta = uu____17302;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17303;
                         FStar_Syntax_Syntax.fv_delta = uu____17304;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17305);_}
                       -> true
                   | uu____17312 -> false in
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
                   let uu____17457 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17457 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17544 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17583 ->
                                 let uu____17584 =
                                   let uu____17585 = is_cons head1 in
                                   Prims.op_Negation uu____17585 in
                                 FStar_Util.Inr uu____17584)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17610 =
                              let uu____17611 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17611.FStar_Syntax_Syntax.n in
                            (match uu____17610 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17629 ->
                                 let uu____17630 =
                                   let uu____17631 = is_cons head1 in
                                   Prims.op_Negation uu____17631 in
                                 FStar_Util.Inr uu____17630))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17700)::rest_a,(p1,uu____17703)::rest_p) ->
                       let uu____17747 = matches_pat t1 p1 in
                       (match uu____17747 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17796 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17902 = matches_pat scrutinee1 p1 in
                       (match uu____17902 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17942  ->
                                  let uu____17943 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17944 =
                                    let uu____17945 =
                                      FStar_List.map
                                        (fun uu____17955  ->
                                           match uu____17955 with
                                           | (uu____17960,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17945
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17943 uu____17944);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17991  ->
                                       match uu____17991 with
                                       | (bv,t1) ->
                                           let uu____18014 =
                                             let uu____18021 =
                                               let uu____18024 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18024 in
                                             let uu____18025 =
                                               let uu____18026 =
                                                 let uu____18057 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18057, false) in
                                               Clos uu____18026 in
                                             (uu____18021, uu____18025) in
                                           uu____18014 :: env2) env1 s in
                              let uu____18174 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18174))) in
                 let uu____18175 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18175
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18196  ->
                match uu___87_18196 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18200 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18206 -> d in
      let uu____18209 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18211 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations) in
           Prims.op_Negation uu____18211) in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18209
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
            let uu___150_18236 = config s e in
            {
              steps = (uu___150_18236.steps);
              tcenv = (uu___150_18236.tcenv);
              delta_level = (uu___150_18236.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18236.strong);
              memoize_lazy = (uu___150_18236.memoize_lazy);
              normalize_pure_lets = (uu___150_18236.normalize_pure_lets)
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
      fun t  -> let uu____18261 = config s e in norm_comp uu____18261 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18274 = config [] env in norm_universe uu____18274 [] u
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
        let uu____18292 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18292 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18299 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18318 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18318.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18318.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18325 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18325
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
                  let uu___152_18334 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18334.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18334.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18334.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___153_18336 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18336.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18336.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18336.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18336.FStar_Syntax_Syntax.flags)
                  } in
            let uu___154_18337 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18337.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18337.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18339 -> c
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
        let uu____18351 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18351 in
      let uu____18358 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18358
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18362  ->
                 let uu____18363 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18363)
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
            ((let uu____18380 =
                let uu____18385 =
                  let uu____18386 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18386 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18385) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18380);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18397 = config [AllowUnboundUniverses] env in
          norm_comp uu____18397 [] c
        with
        | e ->
            ((let uu____18410 =
                let uu____18415 =
                  let uu____18416 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18416 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18415) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18410);
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
                   let uu____18453 =
                     let uu____18454 =
                       let uu____18461 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18461) in
                     FStar_Syntax_Syntax.Tm_refine uu____18454 in
                   mk uu____18453 t01.FStar_Syntax_Syntax.pos
               | uu____18466 -> t2)
          | uu____18467 -> t2 in
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
        let uu____18507 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18507 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18536 ->
                 let uu____18543 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18543 with
                  | (actuals,uu____18553,uu____18554) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18568 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18568 with
                         | (binders,args) ->
                             let uu____18585 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18585
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
      | uu____18593 ->
          let uu____18594 = FStar_Syntax_Util.head_and_args t in
          (match uu____18594 with
           | (head1,args) ->
               let uu____18631 =
                 let uu____18632 = FStar_Syntax_Subst.compress head1 in
                 uu____18632.FStar_Syntax_Syntax.n in
               (match uu____18631 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18635,thead) ->
                    let uu____18661 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18661 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18703 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18711 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18711.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18711.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18711.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18711.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18711.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18711.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18711.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18711.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18711.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18711.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18711.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18711.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18711.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18711.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18711.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18711.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18711.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18711.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18711.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18711.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18711.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18711.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18711.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18711.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18711.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18711.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18711.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18711.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18711.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18711.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18711.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18703 with
                            | (uu____18712,ty,uu____18714) ->
                                eta_expand_with_type env t ty))
                | uu____18715 ->
                    let uu____18716 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18724 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18724.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18724.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18724.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18724.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18724.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18724.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18724.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18724.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18724.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18724.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18724.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18724.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18724.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18724.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18724.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18724.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18724.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18724.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18724.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18724.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18724.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18724.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18724.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18724.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18724.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18724.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18724.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18724.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18724.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18724.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18724.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18716 with
                     | (uu____18725,ty,uu____18727) ->
                         eta_expand_with_type env t ty)))
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
            | (uu____18801,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18807,FStar_Util.Inl t) ->
                let uu____18813 =
                  let uu____18816 =
                    let uu____18817 =
                      let uu____18830 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18830) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18817 in
                  FStar_Syntax_Syntax.mk uu____18816 in
                uu____18813 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18834 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18834 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18861 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18916 ->
                    let uu____18917 =
                      let uu____18926 =
                        let uu____18927 = FStar_Syntax_Subst.compress t3 in
                        uu____18927.FStar_Syntax_Syntax.n in
                      (uu____18926, tc) in
                    (match uu____18917 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18952) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18989) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19028,FStar_Util.Inl uu____19029) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19052 -> failwith "Impossible") in
              (match uu____18861 with
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
          let uu____19157 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19157 with
          | (univ_names1,binders1,tc) ->
              let uu____19215 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19215)
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
          let uu____19250 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19250 with
          | (univ_names1,binders1,tc) ->
              let uu____19310 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19310)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19343 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19343 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19371 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19371.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19371.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19371.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19371.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19392 = s in
          let uu____19393 =
            let uu____19394 =
              let uu____19403 = FStar_List.map (elim_uvars env) sigs in
              (uu____19403, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19394 in
          {
            FStar_Syntax_Syntax.sigel = uu____19393;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19392.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19392.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19392.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19392.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19420 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19420 with
           | (univ_names1,uu____19438,typ1) ->
               let uu___163_19452 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19452.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19452.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19452.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19452.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19458 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19458 with
           | (univ_names1,uu____19476,typ1) ->
               let uu___164_19490 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19490.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19490.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19490.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19490.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19524 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19524 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19547 =
                            let uu____19548 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19548 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19547 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___165_19551 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19551.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19551.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___166_19552 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19552.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19552.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19552.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19552.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19564 = s in
          let uu____19565 =
            let uu____19566 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19566 in
          {
            FStar_Syntax_Syntax.sigel = uu____19565;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19564.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19564.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19564.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19564.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19570 = elim_uvars_aux_t env us [] t in
          (match uu____19570 with
           | (us1,uu____19588,t1) ->
               let uu___168_19602 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19602.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19602.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19602.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19602.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19603 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19605 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19605 with
           | (univs1,binders,signature) ->
               let uu____19633 =
                 let uu____19642 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19642 with
                 | (univs_opening,univs2) ->
                     let uu____19669 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19669) in
               (match uu____19633 with
                | (univs_opening,univs_closing) ->
                    let uu____19686 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19692 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19693 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19692, uu____19693) in
                    (match uu____19686 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19715 =
                           match uu____19715 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19733 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19733 with
                                | (us1,t1) ->
                                    let uu____19744 =
                                      let uu____19749 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19756 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19749, uu____19756) in
                                    (match uu____19744 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19769 =
                                           let uu____19774 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19783 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19774, uu____19783) in
                                         (match uu____19769 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19799 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19799 in
                                              let uu____19800 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19800 with
                                               | (uu____19821,uu____19822,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19837 =
                                                       let uu____19838 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19838 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19837 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19843 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19843 with
                           | (uu____19856,uu____19857,t1) -> t1 in
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
                             | uu____19917 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19934 =
                               let uu____19935 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19935.FStar_Syntax_Syntax.n in
                             match uu____19934 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19994 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20023 =
                               let uu____20024 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20024.FStar_Syntax_Syntax.n in
                             match uu____20023 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20045) ->
                                 let uu____20066 = destruct_action_body body in
                                 (match uu____20066 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20111 ->
                                 let uu____20112 = destruct_action_body t in
                                 (match uu____20112 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20161 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20161 with
                           | (action_univs,t) ->
                               let uu____20170 = destruct_action_typ_templ t in
                               (match uu____20170 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20211 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20211.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20211.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20213 = ed in
                           let uu____20214 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20215 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20216 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20217 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20218 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20219 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20220 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20221 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20222 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20223 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20224 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20225 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20226 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20227 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20213.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20213.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20214;
                             FStar_Syntax_Syntax.bind_wp = uu____20215;
                             FStar_Syntax_Syntax.if_then_else = uu____20216;
                             FStar_Syntax_Syntax.ite_wp = uu____20217;
                             FStar_Syntax_Syntax.stronger = uu____20218;
                             FStar_Syntax_Syntax.close_wp = uu____20219;
                             FStar_Syntax_Syntax.assert_p = uu____20220;
                             FStar_Syntax_Syntax.assume_p = uu____20221;
                             FStar_Syntax_Syntax.null_wp = uu____20222;
                             FStar_Syntax_Syntax.trivial = uu____20223;
                             FStar_Syntax_Syntax.repr = uu____20224;
                             FStar_Syntax_Syntax.return_repr = uu____20225;
                             FStar_Syntax_Syntax.bind_repr = uu____20226;
                             FStar_Syntax_Syntax.actions = uu____20227
                           } in
                         let uu___171_20230 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20230.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20230.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20230.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20230.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20247 =
            match uu___88_20247 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20274 = elim_uvars_aux_t env us [] t in
                (match uu____20274 with
                 | (us1,uu____20298,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___172_20317 = sub_eff in
            let uu____20318 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20321 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20317.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20317.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20318;
              FStar_Syntax_Syntax.lift = uu____20321
            } in
          let uu___173_20324 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20324.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20324.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20324.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20324.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20334 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20334 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20368 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20368.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20368.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20368.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20368.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20379 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t