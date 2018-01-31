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
  fun projectee  -> match projectee with | Beta  -> true | uu____18 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____22 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____26 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____31 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____42 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____46 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____50 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____54 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____58 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____62 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____67 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____81 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____98 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____102 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____106 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____110 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____114 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____118 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____122 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____126 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____130 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____134 -> false
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____168  -> []) }
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
    match projectee with | Clos _0 -> true | uu____369 -> false
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
    match projectee with | Univ _0 -> true | uu____471 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____482 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___72_501  ->
    match uu___72_501 with
    | Clos (uu____502,t,uu____504,uu____505) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____550 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____830 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____866 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____902 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____971 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1013 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1069 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1109 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1141 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1177 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1193 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1218 .
    'Auu____1218 ->
      FStar_Range.range -> 'Auu____1218 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1272 = FStar_ST.op_Bang r in
          match uu____1272 with
          | FStar_Pervasives_Native.Some uu____1320 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1374 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1374 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___73_1381  ->
    match uu___73_1381 with
    | Arg (c,uu____1383,uu____1384) ->
        let uu____1385 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1385
    | MemoLazy uu____1386 -> "MemoLazy"
    | Abs (uu____1393,bs,uu____1395,uu____1396,uu____1397) ->
        let uu____1402 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1402
    | UnivArgs uu____1407 -> "UnivArgs"
    | Match uu____1414 -> "Match"
    | App (uu____1421,t,uu____1423,uu____1424) ->
        let uu____1425 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1425
    | Meta (m,uu____1427) -> "Meta"
    | Let uu____1428 -> "Let"
    | Cfg uu____1437 -> "Cfg"
    | Debug (t,uu____1439) ->
        let uu____1440 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1440
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1448 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1448 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1464 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1464 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1477 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1477 then f () else ()
let is_empty: 'Auu____1481 . 'Auu____1481 Prims.list -> Prims.bool =
  fun uu___74_1487  ->
    match uu___74_1487 with | [] -> true | uu____1490 -> false
let lookup_bvar:
  'Auu____1497 'Auu____1498 .
    ('Auu____1498,'Auu____1497) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1497
  =
  fun env  ->
    fun x  ->
      try
        let uu____1522 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1522
      with
      | uu____1535 ->
          let uu____1536 =
            let uu____1537 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1537 in
          failwith uu____1536
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
          let uu____1574 =
            FStar_List.fold_left
              (fun uu____1600  ->
                 fun u1  ->
                   match uu____1600 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1625 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1625 with
                        | (k_u,n1) ->
                            let uu____1640 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1640
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1574 with
          | (uu____1658,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1683 =
                   let uu____1684 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1684 in
                 match uu____1683 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1702 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1711 ->
                   let uu____1712 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1712
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1718 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1727 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1736 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1743 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1743 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1760 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1760 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1768 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1776 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1776 with
                                  | (uu____1781,m) -> n1 <= m)) in
                        if uu____1768 then rest1 else us1
                    | uu____1786 -> us1)
               | uu____1791 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1795 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1795 in
        let uu____1798 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1798
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1800 = aux u in
           match uu____1800 with
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
          (fun uu____1904  ->
             let uu____1905 = FStar_Syntax_Print.tag_of_term t in
             let uu____1906 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1905
               uu____1906);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1913 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1915 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1940 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1941 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1942 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1943 ->
                  let uu____1960 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1960
                  then
                    let uu____1961 =
                      let uu____1962 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1963 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1962 uu____1963 in
                    failwith uu____1961
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1966 =
                    let uu____1967 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1967 in
                  mk uu____1966 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1974 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1974
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1976 = lookup_bvar env x in
                  (match uu____1976 with
                   | Univ uu____1979 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1982,uu____1983) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2095 = closures_as_binders_delayed cfg env bs in
                  (match uu____2095 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2123 =
                         let uu____2124 =
                           let uu____2141 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2141) in
                         FStar_Syntax_Syntax.Tm_abs uu____2124 in
                       mk uu____2123 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2172 = closures_as_binders_delayed cfg env bs in
                  (match uu____2172 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2214 =
                    let uu____2225 =
                      let uu____2232 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2232] in
                    closures_as_binders_delayed cfg env uu____2225 in
                  (match uu____2214 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2250 =
                         let uu____2251 =
                           let uu____2258 =
                             let uu____2259 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2259
                               FStar_Pervasives_Native.fst in
                           (uu____2258, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2251 in
                       mk uu____2250 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2350 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2350
                    | FStar_Util.Inr c ->
                        let uu____2364 = close_comp cfg env c in
                        FStar_Util.Inr uu____2364 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2380 =
                    let uu____2381 =
                      let uu____2408 = closure_as_term_delayed cfg env t11 in
                      (uu____2408, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2381 in
                  mk uu____2380 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2459 =
                    let uu____2460 =
                      let uu____2467 = closure_as_term_delayed cfg env t' in
                      let uu____2470 =
                        let uu____2471 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2471 in
                      (uu____2467, uu____2470) in
                    FStar_Syntax_Syntax.Tm_meta uu____2460 in
                  mk uu____2459 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2531 =
                    let uu____2532 =
                      let uu____2539 = closure_as_term_delayed cfg env t' in
                      let uu____2542 =
                        let uu____2543 =
                          let uu____2550 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2550) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2543 in
                      (uu____2539, uu____2542) in
                    FStar_Syntax_Syntax.Tm_meta uu____2532 in
                  mk uu____2531 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2569 =
                    let uu____2570 =
                      let uu____2577 = closure_as_term_delayed cfg env t' in
                      let uu____2580 =
                        let uu____2581 =
                          let uu____2590 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2590) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2581 in
                      (uu____2577, uu____2580) in
                    FStar_Syntax_Syntax.Tm_meta uu____2570 in
                  mk uu____2569 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2603 =
                    let uu____2604 =
                      let uu____2611 = closure_as_term_delayed cfg env t' in
                      (uu____2611, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2604 in
                  mk uu____2603 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2651  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2670 =
                    let uu____2681 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2681
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2700 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___93_2712 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2712.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2712.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2700)) in
                  (match uu____2670 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2728 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2728.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2728.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2739,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2798  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2823 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2823
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2843  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2865 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2865
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___95_2877 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2877.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2877.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___96_2878 = lb in
                    let uu____2879 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2878.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2878.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2879
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2909  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2998 =
                    match uu____2998 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3053 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3074 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3134  ->
                                        fun uu____3135  ->
                                          match (uu____3134, uu____3135) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3226 =
                                                norm_pat env3 p1 in
                                              (match uu____3226 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3074 with
                               | (pats1,env3) ->
                                   ((let uu___97_3308 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3308.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3327 = x in
                                let uu____3328 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3327.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3327.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3328
                                } in
                              ((let uu___99_3342 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3342.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3353 = x in
                                let uu____3354 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3353.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3353.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3354
                                } in
                              ((let uu___101_3368 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3368.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3384 = x in
                                let uu____3385 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3384.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3384.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3385
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___103_3392 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3392.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3395 = norm_pat env1 pat in
                        (match uu____3395 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3424 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3424 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3430 =
                    let uu____3431 =
                      let uu____3454 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3454) in
                    FStar_Syntax_Syntax.Tm_match uu____3431 in
                  mk uu____3430 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3540 -> closure_as_term cfg env t
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
        | uu____3566 ->
            FStar_List.map
              (fun uu____3583  ->
                 match uu____3583 with
                 | (x,imp) ->
                     let uu____3602 = closure_as_term_delayed cfg env x in
                     (uu____3602, imp)) args
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
        let uu____3616 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3665  ->
                  fun uu____3666  ->
                    match (uu____3665, uu____3666) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___104_3736 = b in
                          let uu____3737 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3736.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3736.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3737
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3616 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3830 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3843 = closure_as_term_delayed cfg env t in
                 let uu____3844 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3843 uu____3844
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3857 = closure_as_term_delayed cfg env t in
                 let uu____3858 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3857 uu____3858
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
                        (fun uu___75_3884  ->
                           match uu___75_3884 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3888 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3888
                           | f -> f)) in
                 let uu____3892 =
                   let uu___105_3893 = c1 in
                   let uu____3894 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3894;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3893.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3892)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_3904  ->
            match uu___76_3904 with
            | FStar_Syntax_Syntax.DECREASES uu____3905 -> false
            | uu____3908 -> true))
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
                   (fun uu___77_3926  ->
                      match uu___77_3926 with
                      | FStar_Syntax_Syntax.DECREASES uu____3927 -> false
                      | uu____3930 -> true)) in
            let rc1 =
              let uu___106_3932 = rc in
              let uu____3933 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3932.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3933;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3940 -> lopt
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
    let uu____4025 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4025 in
  let arg_as_bounded_int uu____4053 =
    match uu____4053 with
    | (a,uu____4065) ->
        let uu____4072 =
          let uu____4073 = FStar_Syntax_Subst.compress a in
          uu____4073.FStar_Syntax_Syntax.n in
        (match uu____4072 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4083;
                FStar_Syntax_Syntax.vars = uu____4084;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4086;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4087;_},uu____4088)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4127 =
               let uu____4132 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4132) in
             FStar_Pervasives_Native.Some uu____4127
         | uu____4137 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4177 = f a in FStar_Pervasives_Native.Some uu____4177
    | uu____4178 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4226 = f a0 a1 in FStar_Pervasives_Native.Some uu____4226
    | uu____4227 -> FStar_Pervasives_Native.None in
  let unary_op a413 a414 a415 a416 a417 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4269 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a412  -> (Obj.magic (f res.psc_range)) a412)
                    uu____4269)) a413 a414 a415 a416 a417 in
  let binary_op a420 a421 a422 a423 a424 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4318 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a418  ->
                       fun a419  -> (Obj.magic (f res.psc_range)) a418 a419)
                    uu____4318)) a420 a421 a422 a423 a424 in
  let as_primitive_step uu____4342 =
    match uu____4342 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op () (fun a425  -> (Obj.magic arg_as_int) a425)
      (fun a426  ->
         fun a427  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4390 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4390)) a426 a427) in
  let binary_int_op f =
    binary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           fun a431  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4418 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4418)) a429
               a430 a431) in
  let unary_bool_op f =
    unary_op () (fun a432  -> (Obj.magic arg_as_bool) a432)
      (fun a433  ->
         fun a434  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4439 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4439)) a433
             a434) in
  let binary_bool_op f =
    binary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           fun a438  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4467 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4467)) a436
               a437 a438) in
  let binary_string_op f =
    binary_op () (fun a439  -> (Obj.magic arg_as_string) a439)
      (fun a440  ->
         fun a441  ->
           fun a442  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4495 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4495))
               a440 a441 a442) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4603 =
          let uu____4612 = as_a a in
          let uu____4615 = as_b b in (uu____4612, uu____4615) in
        (match uu____4603 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4630 =
               let uu____4631 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4631 in
             FStar_Pervasives_Native.Some uu____4630
         | uu____4632 -> FStar_Pervasives_Native.None)
    | uu____4641 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4655 =
        let uu____4656 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4656 in
      mk uu____4655 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4666 =
      let uu____4669 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4669 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4666 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4701 =
      let uu____4702 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4702 in
    FStar_Syntax_Embeddings.embed_int rng uu____4701 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4720 = arg_as_string a1 in
        (match uu____4720 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4726 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4726 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4739 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4739
              | uu____4740 -> FStar_Pervasives_Native.None)
         | uu____4745 -> FStar_Pervasives_Native.None)
    | uu____4748 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4758 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4758 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4782 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4793 =
          let uu____4814 = arg_as_string fn in
          let uu____4817 = arg_as_int from_line in
          let uu____4820 = arg_as_int from_col in
          let uu____4823 = arg_as_int to_line in
          let uu____4826 = arg_as_int to_col in
          (uu____4814, uu____4817, uu____4820, uu____4823, uu____4826) in
        (match uu____4793 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4857 =
                 let uu____4858 = FStar_BigInt.to_int_fs from_l in
                 let uu____4859 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4858 uu____4859 in
               let uu____4860 =
                 let uu____4861 = FStar_BigInt.to_int_fs to_l in
                 let uu____4862 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4861 uu____4862 in
               FStar_Range.mk_range fn1 uu____4857 uu____4860 in
             let uu____4863 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4863
         | uu____4868 -> FStar_Pervasives_Native.None)
    | uu____4889 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4916)::(a1,uu____4918)::(a2,uu____4920)::[] ->
        let uu____4957 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4957 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4970 -> FStar_Pervasives_Native.None)
    | uu____4971 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4998)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5007 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5031 =
      let uu____5046 =
        let uu____5061 =
          let uu____5076 =
            let uu____5091 =
              let uu____5106 =
                let uu____5121 =
                  let uu____5136 =
                    let uu____5151 =
                      let uu____5166 =
                        let uu____5181 =
                          let uu____5196 =
                            let uu____5211 =
                              let uu____5226 =
                                let uu____5241 =
                                  let uu____5256 =
                                    let uu____5271 =
                                      let uu____5286 =
                                        let uu____5301 =
                                          let uu____5316 =
                                            let uu____5331 =
                                              let uu____5346 =
                                                let uu____5359 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5359,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a443  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a443)
                                                     (fun a444  ->
                                                        fun a445  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a444 a445))) in
                                              let uu____5366 =
                                                let uu____5381 =
                                                  let uu____5394 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5394,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a446  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a446)
                                                       (fun a447  ->
                                                          fun a448  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a447 a448))) in
                                                let uu____5401 =
                                                  let uu____5416 =
                                                    let uu____5431 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5431,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5440 =
                                                    let uu____5457 =
                                                      let uu____5472 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5472,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5481 =
                                                      let uu____5498 =
                                                        let uu____5517 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5517,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5498] in
                                                    uu____5457 :: uu____5481 in
                                                  uu____5416 :: uu____5440 in
                                                uu____5381 :: uu____5401 in
                                              uu____5346 :: uu____5366 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5331 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5316 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a449  ->
                                                (Obj.magic arg_as_string)
                                                  a449)
                                             (fun a450  ->
                                                fun a451  ->
                                                  fun a452  ->
                                                    (Obj.magic
                                                       string_compare') a450
                                                      a451 a452)))
                                          :: uu____5301 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a453  ->
                                              (Obj.magic arg_as_bool) a453)
                                           (fun a454  ->
                                              fun a455  ->
                                                (Obj.magic string_of_bool1)
                                                  a454 a455)))
                                        :: uu____5286 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a456  ->
                                            (Obj.magic arg_as_int) a456)
                                         (fun a457  ->
                                            fun a458  ->
                                              (Obj.magic string_of_int1) a457
                                                a458)))
                                      :: uu____5271 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a459  ->
                                          (Obj.magic arg_as_int) a459)
                                       (fun a460  ->
                                          (Obj.magic arg_as_char) a460)
                                       (fun a461  ->
                                          fun a462  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a461 a462)
                                       (fun a463  ->
                                          fun a464  ->
                                            fun a465  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____5734 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5734 y)) a463
                                                a464 a465)))
                                    :: uu____5256 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5241 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5226 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5211 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5196 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5181 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5166 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a466  -> (Obj.magic arg_as_int) a466)
                         (fun a467  ->
                            fun a468  ->
                              fun a469  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____5901 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5901)) a467 a468 a469)))
                      :: uu____5151 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a470  -> (Obj.magic arg_as_int) a470)
                       (fun a471  ->
                          fun a472  ->
                            fun a473  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5927 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5927)) a471 a472 a473)))
                    :: uu____5136 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a474  -> (Obj.magic arg_as_int) a474)
                     (fun a475  ->
                        fun a476  ->
                          fun a477  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5953 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5953)) a475 a476 a477)))
                  :: uu____5121 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a478  -> (Obj.magic arg_as_int) a478)
                   (fun a479  ->
                      fun a480  ->
                        fun a481  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5979 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5979)) a479 a480 a481)))
                :: uu____5106 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5091 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5076 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5061 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5046 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5031 in
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
      let uu____6129 =
        let uu____6130 =
          let uu____6131 = FStar_Syntax_Syntax.as_arg c in [uu____6131] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6130 in
      uu____6129 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6166 =
              let uu____6179 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6179, (Prims.parse_int "2"),
                (binary_op ()
                   (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                   (fun a483  ->
                      fun a484  ->
                        fun a485  ->
                          (Obj.magic
                             (fun r  ->
                                fun uu____6195  ->
                                  fun uu____6196  ->
                                    match (uu____6195, uu____6196) with
                                    | ((int_to_t1,x),(uu____6215,y)) ->
                                        let uu____6225 =
                                          FStar_BigInt.add_big_int x y in
                                        int_as_bounded r int_to_t1 uu____6225))
                            a483 a484 a485))) in
            let uu____6226 =
              let uu____6241 =
                let uu____6254 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6254, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a486  -> (Obj.magic arg_as_bounded_int) a486)
                     (fun a487  ->
                        fun a488  ->
                          fun a489  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6270  ->
                                    fun uu____6271  ->
                                      match (uu____6270, uu____6271) with
                                      | ((int_to_t1,x),(uu____6290,y)) ->
                                          let uu____6300 =
                                            FStar_BigInt.sub_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6300)) a487 a488 a489))) in
              let uu____6301 =
                let uu____6316 =
                  let uu____6329 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6329, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a490  -> (Obj.magic arg_as_bounded_int) a490)
                       (fun a491  ->
                          fun a492  ->
                            fun a493  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6345  ->
                                      fun uu____6346  ->
                                        match (uu____6345, uu____6346) with
                                        | ((int_to_t1,x),(uu____6365,y)) ->
                                            let uu____6375 =
                                              FStar_BigInt.mult_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6375)) a491 a492 a493))) in
                [uu____6316] in
              uu____6241 :: uu____6301 in
            uu____6166 :: uu____6226)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6465)::(a1,uu____6467)::(a2,uu____6469)::[] ->
        let uu____6506 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6506 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6512 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6512.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6512.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6516 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6516.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6516.FStar_Syntax_Syntax.vars)
                })
         | uu____6517 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6519)::uu____6520::(a1,uu____6522)::(a2,uu____6524)::[] ->
        let uu____6573 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6573 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6579 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6579.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6579.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6583 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6583.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6583.FStar_Syntax_Syntax.vars)
                })
         | uu____6584 -> FStar_Pervasives_Native.None)
    | uu____6585 -> failwith "Unexpected number of arguments" in
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
      let uu____6604 =
        let uu____6605 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6605 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6604
    with | uu____6611 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6615 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6615) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6675  ->
           fun subst1  ->
             match uu____6675 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6716,uu____6717)) ->
                      let uu____6776 = b in
                      (match uu____6776 with
                       | (bv,uu____6784) ->
                           let uu____6785 =
                             let uu____6786 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6786 in
                           if uu____6785
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6791 = unembed_binder term1 in
                              match uu____6791 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6798 =
                                      let uu___111_6799 = bv in
                                      let uu____6800 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_6799.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_6799.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6800
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6798 in
                                  let b_for_x =
                                    let uu____6804 =
                                      let uu____6811 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6811) in
                                    FStar_Syntax_Syntax.NT uu____6804 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_6820  ->
                                         match uu___78_6820 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6821,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6823;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6824;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6829 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6830 -> subst1)) env []
let reduce_primops:
  'Auu____6847 'Auu____6848 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6848) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6847 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6889 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6889
          then tm
          else
            (let uu____6891 = FStar_Syntax_Util.head_and_args tm in
             match uu____6891 with
             | (head1,args) ->
                 let uu____6928 =
                   let uu____6929 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6929.FStar_Syntax_Syntax.n in
                 (match uu____6928 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6933 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6933 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6950  ->
                                   let uu____6951 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6952 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6959 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6951 uu____6952 uu____6959);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6964  ->
                                   let uu____6965 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6965);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6968  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6970 =
                                 prim_step.interpretation psc args in
                               match uu____6970 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6976  ->
                                         let uu____6977 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6977);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6983  ->
                                         let uu____6984 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6985 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6984 uu____6985);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6986 ->
                           (log_primops cfg
                              (fun uu____6990  ->
                                 let uu____6991 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6991);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6995  ->
                            let uu____6996 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6996);
                       (match args with
                        | (a1,uu____6998)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7015 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7027  ->
                            let uu____7028 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7028);
                       (match args with
                        | (t,uu____7030)::(r,uu____7032)::[] ->
                            let uu____7059 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7059 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7063 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7063.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7063.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7066 -> tm))
                  | uu____7075 -> tm))
let reduce_equality:
  'Auu____7080 'Auu____7081 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7081) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7080 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7119 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___113_7119.tcenv);
           delta_level = (uu___113_7119.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7119.strong);
           memoize_lazy = (uu___113_7119.memoize_lazy);
           normalize_pure_lets = (uu___113_7119.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____7126 'Auu____7127 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7127) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7126 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7169 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7169
          then tm1
          else
            (let w t =
               let uu___114_7181 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7181.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7181.FStar_Syntax_Syntax.vars)
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
               | uu____7198 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7203 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7203
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7224 =
                 match uu____7224 with
                 | (t1,q) ->
                     let uu____7237 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7237 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7265 -> (t1, q)) in
               let uu____7274 = FStar_Syntax_Util.head_and_args t in
               match uu____7274 with
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
                         FStar_Syntax_Syntax.pos = uu____7371;
                         FStar_Syntax_Syntax.vars = uu____7372;_},uu____7373);
                    FStar_Syntax_Syntax.pos = uu____7374;
                    FStar_Syntax_Syntax.vars = uu____7375;_},args)
                 ->
                 let uu____7401 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7401
                 then
                   let uu____7402 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7402 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7457)::
                        (uu____7458,(arg,uu____7460))::[] ->
                        maybe_auto_squash arg
                    | (uu____7525,(arg,uu____7527))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7528)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7593)::uu____7594::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7657::(FStar_Pervasives_Native.Some (false
                                   ),uu____7658)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7721 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7737 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7737
                    then
                      let uu____7738 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7738 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7793)::uu____7794::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7857::(FStar_Pervasives_Native.Some (true
                                     ),uu____7858)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7921)::
                          (uu____7922,(arg,uu____7924))::[] ->
                          maybe_auto_squash arg
                      | (uu____7989,(arg,uu____7991))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7992)::[]
                          -> maybe_auto_squash arg
                      | uu____8057 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8073 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8073
                       then
                         let uu____8074 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8074 with
                         | uu____8129::(FStar_Pervasives_Native.Some (true
                                        ),uu____8130)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8193)::uu____8194::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8257)::
                             (uu____8258,(arg,uu____8260))::[] ->
                             maybe_auto_squash arg
                         | (uu____8325,(p,uu____8327))::(uu____8328,(q,uu____8330))::[]
                             ->
                             let uu____8395 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8395
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8397 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8413 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8413
                          then
                            let uu____8414 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8414 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8469)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8508)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8547 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8563 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8563
                             then
                               match args with
                               | (t,uu____8565)::[] ->
                                   let uu____8582 =
                                     let uu____8583 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8583.FStar_Syntax_Syntax.n in
                                   (match uu____8582 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8586::[],body,uu____8588) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8615 -> tm1)
                                    | uu____8618 -> tm1)
                               | (uu____8619,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8620))::
                                   (t,uu____8622)::[] ->
                                   let uu____8661 =
                                     let uu____8662 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8662.FStar_Syntax_Syntax.n in
                                   (match uu____8661 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8665::[],body,uu____8667) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8694 -> tm1)
                                    | uu____8697 -> tm1)
                               | uu____8698 -> tm1
                             else
                               (let uu____8708 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8708
                                then
                                  match args with
                                  | (t,uu____8710)::[] ->
                                      let uu____8727 =
                                        let uu____8728 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8728.FStar_Syntax_Syntax.n in
                                      (match uu____8727 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8731::[],body,uu____8733)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8760 -> tm1)
                                       | uu____8763 -> tm1)
                                  | (uu____8764,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8765))::(t,uu____8767)::[] ->
                                      let uu____8806 =
                                        let uu____8807 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8807.FStar_Syntax_Syntax.n in
                                      (match uu____8806 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8810::[],body,uu____8812)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8839 -> tm1)
                                       | uu____8842 -> tm1)
                                  | uu____8843 -> tm1
                                else
                                  (let uu____8853 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8853
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8854;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8855;_},uu____8856)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8873;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8874;_},uu____8875)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8892 -> tm1
                                   else
                                     (let uu____8902 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8902 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8922 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8932;
                    FStar_Syntax_Syntax.vars = uu____8933;_},args)
                 ->
                 let uu____8955 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8955
                 then
                   let uu____8956 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8956 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9011)::
                        (uu____9012,(arg,uu____9014))::[] ->
                        maybe_auto_squash arg
                    | (uu____9079,(arg,uu____9081))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9082)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9147)::uu____9148::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9211::(FStar_Pervasives_Native.Some (false
                                   ),uu____9212)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9275 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9291 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9291
                    then
                      let uu____9292 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9292 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9347)::uu____9348::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9411::(FStar_Pervasives_Native.Some (true
                                     ),uu____9412)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9475)::
                          (uu____9476,(arg,uu____9478))::[] ->
                          maybe_auto_squash arg
                      | (uu____9543,(arg,uu____9545))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9546)::[]
                          -> maybe_auto_squash arg
                      | uu____9611 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9627 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9627
                       then
                         let uu____9628 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9628 with
                         | uu____9683::(FStar_Pervasives_Native.Some (true
                                        ),uu____9684)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9747)::uu____9748::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9811)::
                             (uu____9812,(arg,uu____9814))::[] ->
                             maybe_auto_squash arg
                         | (uu____9879,(p,uu____9881))::(uu____9882,(q,uu____9884))::[]
                             ->
                             let uu____9949 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9949
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9951 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9967 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9967
                          then
                            let uu____9968 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9968 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10023)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10062)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10101 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10117 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10117
                             then
                               match args with
                               | (t,uu____10119)::[] ->
                                   let uu____10136 =
                                     let uu____10137 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10137.FStar_Syntax_Syntax.n in
                                   (match uu____10136 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10140::[],body,uu____10142) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10169 -> tm1)
                                    | uu____10172 -> tm1)
                               | (uu____10173,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10174))::
                                   (t,uu____10176)::[] ->
                                   let uu____10215 =
                                     let uu____10216 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10216.FStar_Syntax_Syntax.n in
                                   (match uu____10215 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10219::[],body,uu____10221) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10248 -> tm1)
                                    | uu____10251 -> tm1)
                               | uu____10252 -> tm1
                             else
                               (let uu____10262 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10262
                                then
                                  match args with
                                  | (t,uu____10264)::[] ->
                                      let uu____10281 =
                                        let uu____10282 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10282.FStar_Syntax_Syntax.n in
                                      (match uu____10281 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10285::[],body,uu____10287)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10314 -> tm1)
                                       | uu____10317 -> tm1)
                                  | (uu____10318,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10319))::(t,uu____10321)::[] ->
                                      let uu____10360 =
                                        let uu____10361 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10361.FStar_Syntax_Syntax.n in
                                      (match uu____10360 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10364::[],body,uu____10366)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10393 -> tm1)
                                       | uu____10396 -> tm1)
                                  | uu____10397 -> tm1
                                else
                                  (let uu____10407 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10407
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10408;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10409;_},uu____10410)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10427;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10428;_},uu____10429)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10446 -> tm1
                                   else
                                     (let uu____10456 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10456 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10476 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10485 -> tm1)
let maybe_simplify:
  'Auu____10492 'Auu____10493 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10493) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10492 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10536 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10536
           then
             let uu____10537 = FStar_Syntax_Print.term_to_string tm in
             let uu____10538 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10537 uu____10538
           else ());
          tm'
let is_norm_request:
  'Auu____10544 .
    FStar_Syntax_Syntax.term -> 'Auu____10544 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10557 =
        let uu____10564 =
          let uu____10565 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10565.FStar_Syntax_Syntax.n in
        (uu____10564, args) in
      match uu____10557 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10571::uu____10572::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10576::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10581::uu____10582::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10585 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___79_10596  ->
    match uu___79_10596 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10602 =
          let uu____10605 =
            let uu____10606 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10606 in
          [uu____10605] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10602
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10621 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10621) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10659 =
          let uu____10662 =
            let uu____10667 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10667 s in
          FStar_All.pipe_right uu____10662 FStar_Util.must in
        FStar_All.pipe_right uu____10659 tr_norm_steps in
      match args with
      | uu____10692::(tm,uu____10694)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10717)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10732)::uu____10733::(tm,uu____10735)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10775 =
              let uu____10778 = full_norm steps in parse_steps uu____10778 in
            Beta :: uu____10775 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10787 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___80_10804  ->
    match uu___80_10804 with
    | (App
        (uu____10807,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10808;
                       FStar_Syntax_Syntax.vars = uu____10809;_},uu____10810,uu____10811))::uu____10812
        -> true
    | uu____10819 -> false
let firstn:
  'Auu____10825 .
    Prims.int ->
      'Auu____10825 Prims.list ->
        ('Auu____10825 Prims.list,'Auu____10825 Prims.list)
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
          (uu____10861,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10862;
                         FStar_Syntax_Syntax.vars = uu____10863;_},uu____10864,uu____10865))::uu____10866
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10873 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11020  ->
               let uu____11021 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11022 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11023 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11030 =
                 let uu____11031 =
                   let uu____11034 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11034 in
                 stack_to_string uu____11031 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11021 uu____11022 uu____11023 uu____11030);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11057 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11082 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11099 =
                 let uu____11100 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11101 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11100 uu____11101 in
               failwith uu____11099
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11102 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11119 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11120 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11121;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11122;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11125;
                 FStar_Syntax_Syntax.fv_delta = uu____11126;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11127;
                 FStar_Syntax_Syntax.fv_delta = uu____11128;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11129);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11137 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11137 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11143  ->
                     let uu____11144 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11145 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11144 uu____11145);
                if b
                then
                  (let uu____11146 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11146 t1 fv)
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
                 let uu___115_11185 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11185.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11185.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11218 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11218) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11226 = cfg in
                 let uu____11227 =
                   FStar_List.filter
                     (fun uu___81_11230  ->
                        match uu___81_11230 with
                        | UnfoldOnly uu____11231 -> false
                        | NoDeltaSteps  -> false
                        | uu____11234 -> true) cfg.steps in
                 {
                   steps = uu____11227;
                   tcenv = (uu___116_11226.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11226.primitive_steps);
                   strong = (uu___116_11226.strong);
                   memoize_lazy = (uu___116_11226.memoize_lazy);
                   normalize_pure_lets = true
                 } in
               let uu____11235 = get_norm_request (norm cfg' env []) args in
               (match uu____11235 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11251 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11256  ->
                                match uu___82_11256 with
                                | UnfoldUntil uu____11257 -> true
                                | UnfoldOnly uu____11258 -> true
                                | uu____11261 -> false)) in
                      if uu____11251
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___117_11266 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___117_11266.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11266.primitive_steps);
                        strong = (uu___117_11266.strong);
                        memoize_lazy = (uu___117_11266.memoize_lazy);
                        normalize_pure_lets = true
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11273 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11273
                      then
                        let uu____11276 =
                          let uu____11277 =
                            let uu____11282 = FStar_Util.now () in
                            (t1, uu____11282) in
                          Debug uu____11277 in
                        uu____11276 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11286 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11286
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11293 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11293
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11296 =
                      let uu____11303 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11303, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11296 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11316  ->
                         match uu___83_11316 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11319 =
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
                 if uu____11319
                 then false
                 else
                   (let uu____11321 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11328  ->
                              match uu___84_11328 with
                              | UnfoldOnly uu____11329 -> true
                              | uu____11332 -> false)) in
                    match uu____11321 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11336 -> should_delta) in
               (log cfg
                  (fun uu____11344  ->
                     let uu____11345 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11346 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11347 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11345 uu____11346 uu____11347);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11350 = lookup_bvar env x in
               (match uu____11350 with
                | Univ uu____11353 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11402 = FStar_ST.op_Bang r in
                      (match uu____11402 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11520  ->
                                 let uu____11521 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11522 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11521
                                   uu____11522);
                            (let uu____11523 =
                               let uu____11524 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11524.FStar_Syntax_Syntax.n in
                             match uu____11523 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11527 ->
                                 norm cfg env2 stack t'
                             | uu____11544 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11614)::uu____11615 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11624)::uu____11625 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11635,uu____11636))::stack_rest ->
                    (match c with
                     | Univ uu____11640 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11649 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11670  ->
                                    let uu____11671 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11671);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11711  ->
                                    let uu____11712 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11712);
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
                       (fun uu____11790  ->
                          let uu____11791 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11791);
                     norm cfg env stack1 t1)
                | (Debug uu____11792)::uu____11793 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11800 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11800
                    else
                      (let uu____11802 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11802 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11844  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11872 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11872
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11882 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11882)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11887 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11887.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11887.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11888 -> lopt in
                           (log cfg
                              (fun uu____11894  ->
                                 let uu____11895 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11895);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_11904 = cfg in
                               {
                                 steps = (uu___119_11904.steps);
                                 tcenv = (uu___119_11904.tcenv);
                                 delta_level = (uu___119_11904.delta_level);
                                 primitive_steps =
                                   (uu___119_11904.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_11904.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_11904.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11915)::uu____11916 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11923 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11923
                    else
                      (let uu____11925 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11925 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11967  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11995 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11995
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12005 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12005)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12010 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12010.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12010.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12011 -> lopt in
                           (log cfg
                              (fun uu____12017  ->
                                 let uu____12018 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12018);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12027 = cfg in
                               {
                                 steps = (uu___119_12027.steps);
                                 tcenv = (uu___119_12027.tcenv);
                                 delta_level = (uu___119_12027.delta_level);
                                 primitive_steps =
                                   (uu___119_12027.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12027.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12027.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12038)::uu____12039 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12050 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12050
                    else
                      (let uu____12052 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12052 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12094  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12122 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12122
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12132 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12132)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12137 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12137.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12137.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12138 -> lopt in
                           (log cfg
                              (fun uu____12144  ->
                                 let uu____12145 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12145);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12154 = cfg in
                               {
                                 steps = (uu___119_12154.steps);
                                 tcenv = (uu___119_12154.tcenv);
                                 delta_level = (uu___119_12154.delta_level);
                                 primitive_steps =
                                   (uu___119_12154.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12154.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12154.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12165)::uu____12166 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12177 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12177
                    else
                      (let uu____12179 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12179 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12221  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12249 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12249
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12259 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12259)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12264 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12264.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12264.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12265 -> lopt in
                           (log cfg
                              (fun uu____12271  ->
                                 let uu____12272 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12272);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12281 = cfg in
                               {
                                 steps = (uu___119_12281.steps);
                                 tcenv = (uu___119_12281.tcenv);
                                 delta_level = (uu___119_12281.delta_level);
                                 primitive_steps =
                                   (uu___119_12281.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12281.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12281.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12292)::uu____12293 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12308 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12308
                    else
                      (let uu____12310 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12310 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12352  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12380 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12380
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12390 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12390)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12395 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12395.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12395.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12396 -> lopt in
                           (log cfg
                              (fun uu____12402  ->
                                 let uu____12403 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12403);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12412 = cfg in
                               {
                                 steps = (uu___119_12412.steps);
                                 tcenv = (uu___119_12412.tcenv);
                                 delta_level = (uu___119_12412.delta_level);
                                 primitive_steps =
                                   (uu___119_12412.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12412.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12412.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12423 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12423
                    else
                      (let uu____12425 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12425 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12467  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12495 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12495
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12505 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12505)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12510 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12510.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12510.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12511 -> lopt in
                           (log cfg
                              (fun uu____12517  ->
                                 let uu____12518 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12518);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12527 = cfg in
                               {
                                 steps = (uu___119_12527.steps);
                                 tcenv = (uu___119_12527.tcenv);
                                 delta_level = (uu___119_12527.delta_level);
                                 primitive_steps =
                                   (uu___119_12527.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12527.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12527.normalize_pure_lets)
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
                      (fun uu____12576  ->
                         fun stack1  ->
                           match uu____12576 with
                           | (a,aq) ->
                               let uu____12588 =
                                 let uu____12589 =
                                   let uu____12596 =
                                     let uu____12597 =
                                       let uu____12628 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12628, false) in
                                     Clos uu____12597 in
                                   (uu____12596, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12589 in
                               uu____12588 :: stack1) args) in
               (log cfg
                  (fun uu____12712  ->
                     let uu____12713 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12713);
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
                             ((let uu___120_12749 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_12749.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_12749.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12750 ->
                      let uu____12755 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12755)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12758 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12758 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12789 =
                          let uu____12790 =
                            let uu____12797 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_12799 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_12799.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_12799.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12797) in
                          FStar_Syntax_Syntax.Tm_refine uu____12790 in
                        mk uu____12789 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12818 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12818
               else
                 (let uu____12820 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12820 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12828 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12852  -> dummy :: env1) env) in
                        norm_comp cfg uu____12828 c1 in
                      let t2 =
                        let uu____12874 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12874 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12933)::uu____12934 ->
                    (log cfg
                       (fun uu____12945  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12946)::uu____12947 ->
                    (log cfg
                       (fun uu____12958  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12959,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12960;
                                   FStar_Syntax_Syntax.vars = uu____12961;_},uu____12962,uu____12963))::uu____12964
                    ->
                    (log cfg
                       (fun uu____12973  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12974)::uu____12975 ->
                    (log cfg
                       (fun uu____12986  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12987 ->
                    (log cfg
                       (fun uu____12990  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12994  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13011 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13011
                         | FStar_Util.Inr c ->
                             let uu____13019 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13019 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13032 =
                               let uu____13033 =
                                 let uu____13060 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13060, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13033 in
                             mk uu____13032 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13079 ->
                           let uu____13080 =
                             let uu____13081 =
                               let uu____13082 =
                                 let uu____13109 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13109, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13082 in
                             mk uu____13081 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13080))))
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
                         let uu____13219 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13219 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13239 = cfg in
                               let uu____13240 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___122_13239.steps);
                                 tcenv = uu____13240;
                                 delta_level = (uu___122_13239.delta_level);
                                 primitive_steps =
                                   (uu___122_13239.primitive_steps);
                                 strong = (uu___122_13239.strong);
                                 memoize_lazy = (uu___122_13239.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___122_13239.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____13245 =
                                 let uu____13246 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13246 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13245 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___123_13249 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13249.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13249.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13250 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13250
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13261,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13262;
                               FStar_Syntax_Syntax.lbunivs = uu____13263;
                               FStar_Syntax_Syntax.lbtyp = uu____13264;
                               FStar_Syntax_Syntax.lbeff = uu____13265;
                               FStar_Syntax_Syntax.lbdef = uu____13266;_}::uu____13267),uu____13268)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13304 =
                 (let uu____13307 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13307) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13309 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13309))) in
               if uu____13304
               then
                 let binder =
                   let uu____13311 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13311 in
                 let env1 =
                   let uu____13321 =
                     let uu____13328 =
                       let uu____13329 =
                         let uu____13360 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13360,
                           false) in
                       Clos uu____13329 in
                     ((FStar_Pervasives_Native.Some binder), uu____13328) in
                   uu____13321 :: env in
                 (log cfg
                    (fun uu____13453  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13455 =
                    let uu____13460 =
                      let uu____13461 =
                        let uu____13462 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13462
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13461] in
                    FStar_Syntax_Subst.open_term uu____13460 body in
                  match uu____13455 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13471  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13479 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13479 in
                          FStar_Util.Inl
                            (let uu___124_13489 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13489.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13489.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13492  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13494 = lb in
                           let uu____13495 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13494.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13494.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13495
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13530  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___126_13553 = cfg in
                           {
                             steps = (uu___126_13553.steps);
                             tcenv = (uu___126_13553.tcenv);
                             delta_level = (uu___126_13553.delta_level);
                             primitive_steps =
                               (uu___126_13553.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13553.memoize_lazy);
                             normalize_pure_lets =
                               (uu___126_13553.normalize_pure_lets)
                           } in
                         log cfg1
                           (fun uu____13556  ->
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
               let uu____13573 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13573 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13609 =
                               let uu___127_13610 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13610.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13610.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13609 in
                           let uu____13611 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13611 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13637 =
                                   FStar_List.map (fun uu____13653  -> dummy)
                                     lbs1 in
                                 let uu____13654 =
                                   let uu____13663 =
                                     FStar_List.map
                                       (fun uu____13683  -> dummy) xs1 in
                                   FStar_List.append uu____13663 env in
                                 FStar_List.append uu____13637 uu____13654 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13707 =
                                       let uu___128_13708 = rc in
                                       let uu____13709 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13708.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13709;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13708.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13707
                                 | uu____13716 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___129_13720 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_13720.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_13720.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13730 =
                        FStar_List.map (fun uu____13746  -> dummy) lbs2 in
                      FStar_List.append uu____13730 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13754 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13754 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_13770 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_13770.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_13770.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13797 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13797
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13816 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13892  ->
                        match uu____13892 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14013 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14013.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14013.FStar_Syntax_Syntax.sort)
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
               (match uu____13816 with
                | (rec_env,memos,uu____14226) ->
                    let uu____14279 =
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
                             let uu____14590 =
                               let uu____14597 =
                                 let uu____14598 =
                                   let uu____14629 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14629, false) in
                                 Clos uu____14598 in
                               (FStar_Pervasives_Native.None, uu____14597) in
                             uu____14590 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14739  ->
                     let uu____14740 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14740);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14762 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14764::uu____14765 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14770) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14771 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14802 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14816 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14816
                              | uu____14827 -> m in
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
              let uu____14839 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14839 in
            let uu____14840 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14840 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14853  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14864  ->
                      let uu____14865 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14866 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14865
                        uu____14866);
                 (let t1 =
                    let uu____14868 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14870 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____14870) in
                    if uu____14868
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
                    | (UnivArgs (us',uu____14880))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____14935 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____14938 ->
                        let uu____14941 =
                          let uu____14942 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14942 in
                        failwith uu____14941
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
                let uu____14963 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____14963
                then
                  let uu___132_14964 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_14964.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_14964.primitive_steps);
                    strong = (uu___132_14964.strong);
                    memoize_lazy = (uu___132_14964.memoize_lazy);
                    normalize_pure_lets =
                      (uu___132_14964.normalize_pure_lets)
                  }
                else
                  (let uu___133_14966 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_14966.tcenv);
                     delta_level = (uu___133_14966.delta_level);
                     primitive_steps = (uu___133_14966.primitive_steps);
                     strong = (uu___133_14966.strong);
                     memoize_lazy = (uu___133_14966.memoize_lazy);
                     normalize_pure_lets =
                       (uu___133_14966.normalize_pure_lets)
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
                  (fun uu____14995  ->
                     let uu____14996 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____14997 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14996
                       uu____14997);
                (let uu____14998 =
                   let uu____14999 = FStar_Syntax_Subst.compress head2 in
                   uu____14999.FStar_Syntax_Syntax.n in
                 match uu____14998 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15017 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15017 with
                      | (uu____15018,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15024 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15032 =
                                   let uu____15033 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15033.FStar_Syntax_Syntax.n in
                                 match uu____15032 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15039,uu____15040))
                                     ->
                                     let uu____15049 =
                                       let uu____15050 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15050.FStar_Syntax_Syntax.n in
                                     (match uu____15049 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15056,msrc,uu____15058))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15067 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15067
                                      | uu____15068 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15069 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15070 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15070 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15075 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15075.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15075.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15075.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15076 = FStar_List.tl stack in
                                    let uu____15077 =
                                      let uu____15078 =
                                        let uu____15081 =
                                          let uu____15082 =
                                            let uu____15095 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15095) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15082 in
                                        FStar_Syntax_Syntax.mk uu____15081 in
                                      uu____15078
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15076 uu____15077
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15111 =
                                      let uu____15112 = is_return body in
                                      match uu____15112 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15116;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15117;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15122 -> false in
                                    if uu____15111
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
                                         let uu____15145 =
                                           let uu____15148 =
                                             let uu____15149 =
                                               let uu____15166 =
                                                 let uu____15169 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15169] in
                                               (uu____15166, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15149 in
                                           FStar_Syntax_Syntax.mk uu____15148 in
                                         uu____15145
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15185 =
                                           let uu____15186 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15186.FStar_Syntax_Syntax.n in
                                         match uu____15185 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15192::uu____15193::[])
                                             ->
                                             let uu____15200 =
                                               let uu____15203 =
                                                 let uu____15204 =
                                                   let uu____15211 =
                                                     let uu____15214 =
                                                       let uu____15215 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15215 in
                                                     let uu____15216 =
                                                       let uu____15219 =
                                                         let uu____15220 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15220 in
                                                       [uu____15219] in
                                                     uu____15214 ::
                                                       uu____15216 in
                                                   (bind1, uu____15211) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15204 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15203 in
                                             uu____15200
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15228 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15234 =
                                           let uu____15237 =
                                             let uu____15238 =
                                               let uu____15253 =
                                                 let uu____15256 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15257 =
                                                   let uu____15260 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15261 =
                                                     let uu____15264 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15265 =
                                                       let uu____15268 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15269 =
                                                         let uu____15272 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15273 =
                                                           let uu____15276 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15276] in
                                                         uu____15272 ::
                                                           uu____15273 in
                                                       uu____15268 ::
                                                         uu____15269 in
                                                     uu____15264 ::
                                                       uu____15265 in
                                                   uu____15260 :: uu____15261 in
                                                 uu____15256 :: uu____15257 in
                                               (bind_inst, uu____15253) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15238 in
                                           FStar_Syntax_Syntax.mk uu____15237 in
                                         uu____15234
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15287  ->
                                            let uu____15288 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15288);
                                       (let uu____15289 = FStar_List.tl stack in
                                        norm cfg env uu____15289 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15313 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15313 with
                      | (uu____15314,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15349 =
                                  let uu____15350 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15350.FStar_Syntax_Syntax.n in
                                match uu____15349 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15356) -> t2
                                | uu____15361 -> head3 in
                              let uu____15362 =
                                let uu____15363 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15363.FStar_Syntax_Syntax.n in
                              match uu____15362 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15369 -> FStar_Pervasives_Native.None in
                            let uu____15370 = maybe_extract_fv head3 in
                            match uu____15370 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15380 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15380
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15385 = maybe_extract_fv head4 in
                                  match uu____15385 with
                                  | FStar_Pervasives_Native.Some uu____15390
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15391 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15396 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15411 =
                              match uu____15411 with
                              | (e,q) ->
                                  let uu____15418 =
                                    let uu____15419 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15419.FStar_Syntax_Syntax.n in
                                  (match uu____15418 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15434 -> false) in
                            let uu____15435 =
                              let uu____15436 =
                                let uu____15443 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15443 :: args in
                              FStar_Util.for_some is_arg_impure uu____15436 in
                            if uu____15435
                            then
                              let uu____15448 =
                                let uu____15449 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15449 in
                              failwith uu____15448
                            else ());
                           (let uu____15451 = maybe_unfold_action head_app in
                            match uu____15451 with
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
                                let uu____15488 = FStar_List.tl stack in
                                norm cfg env uu____15488 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15490) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15514 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15514 in
                     (log cfg
                        (fun uu____15518  ->
                           let uu____15519 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15519);
                      (let uu____15520 = FStar_List.tl stack in
                       norm cfg env uu____15520 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15522) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15647  ->
                               match uu____15647 with
                               | (pat,wopt,tm) ->
                                   let uu____15695 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15695))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15727 = FStar_List.tl stack in
                     norm cfg env uu____15727 tm
                 | uu____15728 -> fallback ())
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
              (fun uu____15742  ->
                 let uu____15743 = FStar_Ident.string_of_lid msrc in
                 let uu____15744 = FStar_Ident.string_of_lid mtgt in
                 let uu____15745 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15743
                   uu____15744 uu____15745);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15747 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15747 with
               | (uu____15748,return_repr) ->
                   let return_inst =
                     let uu____15757 =
                       let uu____15758 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15758.FStar_Syntax_Syntax.n in
                     match uu____15757 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15764::[]) ->
                         let uu____15771 =
                           let uu____15774 =
                             let uu____15775 =
                               let uu____15782 =
                                 let uu____15785 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15785] in
                               (return_tm, uu____15782) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15775 in
                           FStar_Syntax_Syntax.mk uu____15774 in
                         uu____15771 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15793 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15796 =
                     let uu____15799 =
                       let uu____15800 =
                         let uu____15815 =
                           let uu____15818 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15819 =
                             let uu____15822 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15822] in
                           uu____15818 :: uu____15819 in
                         (return_inst, uu____15815) in
                       FStar_Syntax_Syntax.Tm_app uu____15800 in
                     FStar_Syntax_Syntax.mk uu____15799 in
                   uu____15796 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15831 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15831 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15834 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15834
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15835;
                     FStar_TypeChecker_Env.mtarget = uu____15836;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15837;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15852;
                     FStar_TypeChecker_Env.mtarget = uu____15853;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15854;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15878 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____15879 = FStar_Syntax_Util.mk_reify e in
                   lift uu____15878 t FStar_Syntax_Syntax.tun uu____15879)
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
                (fun uu____15935  ->
                   match uu____15935 with
                   | (a,imp) ->
                       let uu____15946 = norm cfg env [] a in
                       (uu____15946, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_15960 = comp in
            let uu____15961 =
              let uu____15962 =
                let uu____15971 = norm cfg env [] t in
                let uu____15972 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15971, uu____15972) in
              FStar_Syntax_Syntax.Total uu____15962 in
            {
              FStar_Syntax_Syntax.n = uu____15961;
              FStar_Syntax_Syntax.pos =
                (uu___135_15960.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_15960.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_15987 = comp in
            let uu____15988 =
              let uu____15989 =
                let uu____15998 = norm cfg env [] t in
                let uu____15999 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15998, uu____15999) in
              FStar_Syntax_Syntax.GTotal uu____15989 in
            {
              FStar_Syntax_Syntax.n = uu____15988;
              FStar_Syntax_Syntax.pos =
                (uu___136_15987.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_15987.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16051  ->
                      match uu____16051 with
                      | (a,i) ->
                          let uu____16062 = norm cfg env [] a in
                          (uu____16062, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16073  ->
                      match uu___85_16073 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16077 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16077
                      | f -> f)) in
            let uu___137_16081 = comp in
            let uu____16082 =
              let uu____16083 =
                let uu___138_16084 = ct in
                let uu____16085 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16086 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16089 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16085;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16084.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16086;
                  FStar_Syntax_Syntax.effect_args = uu____16089;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16083 in
            {
              FStar_Syntax_Syntax.n = uu____16082;
              FStar_Syntax_Syntax.pos =
                (uu___137_16081.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16081.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16100  ->
        match uu____16100 with
        | (x,imp) ->
            let uu____16103 =
              let uu___139_16104 = x in
              let uu____16105 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16104.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16104.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16105
              } in
            (uu____16103, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16111 =
          FStar_List.fold_left
            (fun uu____16129  ->
               fun b  ->
                 match uu____16129 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16111 with | (nbs,uu____16169) -> FStar_List.rev nbs
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
            let uu____16185 =
              let uu___140_16186 = rc in
              let uu____16187 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16186.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16187;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16186.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16185
        | uu____16194 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16207  ->
               let uu____16208 = FStar_Syntax_Print.tag_of_term t in
               let uu____16209 = FStar_Syntax_Print.term_to_string t in
               let uu____16210 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16217 =
                 let uu____16218 =
                   let uu____16221 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16221 in
                 stack_to_string uu____16218 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16208 uu____16209 uu____16210 uu____16217);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16250 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16250
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16252 =
                     let uu____16253 =
                       let uu____16254 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16254 in
                     FStar_Util.string_of_int uu____16253 in
                   let uu____16259 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16260 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16252 uu____16259 uu____16260
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16314  ->
                     let uu____16315 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16315);
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
               let uu____16351 =
                 let uu___141_16352 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16352.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16352.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16351
           | (Arg (Univ uu____16353,uu____16354,uu____16355))::uu____16356 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16359,uu____16360))::uu____16361 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16377),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16430  ->
                     let uu____16431 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16431);
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
                  (let uu____16441 = FStar_ST.op_Bang m in
                   match uu____16441 with
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
                   | FStar_Pervasives_Native.Some (uu____16578,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16625 =
                 log cfg
                   (fun uu____16629  ->
                      let uu____16630 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16630);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16634 =
                 let uu____16635 = FStar_Syntax_Subst.compress t in
                 uu____16635.FStar_Syntax_Syntax.n in
               (match uu____16634 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16662 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16662 in
                    (log cfg
                       (fun uu____16666  ->
                          let uu____16667 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16667);
                     (let uu____16668 = FStar_List.tl stack in
                      norm cfg env1 uu____16668 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16669);
                       FStar_Syntax_Syntax.pos = uu____16670;
                       FStar_Syntax_Syntax.vars = uu____16671;_},(e,uu____16673)::[])
                    -> norm cfg env1 stack' e
                | uu____16702 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16713 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16713
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16725  ->
                     let uu____16726 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16726);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16731 =
                   log cfg
                     (fun uu____16736  ->
                        let uu____16737 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16738 =
                          let uu____16739 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16756  ->
                                    match uu____16756 with
                                    | (p,uu____16766,uu____16767) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16739
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16737 uu____16738);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_16784  ->
                                match uu___86_16784 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16785 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___142_16789 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_16789.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_16789.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_16789.memoize_lazy);
                        normalize_pure_lets =
                          (uu___142_16789.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16821 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16842 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16902  ->
                                    fun uu____16903  ->
                                      match (uu____16902, uu____16903) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____16994 = norm_pat env3 p1 in
                                          (match uu____16994 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16842 with
                           | (pats1,env3) ->
                               ((let uu___143_17076 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17076.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17095 = x in
                            let uu____17096 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17095.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17095.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17096
                            } in
                          ((let uu___145_17110 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17110.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17121 = x in
                            let uu____17122 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17121.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17121.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17122
                            } in
                          ((let uu___147_17136 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17136.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___148_17152 = x in
                            let uu____17153 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17152.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17152.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17153
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___149_17160 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17160.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17170 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17184 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17184 with
                                  | (p,wopt,e) ->
                                      let uu____17204 = norm_pat env1 p in
                                      (match uu____17204 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17229 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17229 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17235 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17235) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17245) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17250 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17251;
                         FStar_Syntax_Syntax.fv_delta = uu____17252;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17253;
                         FStar_Syntax_Syntax.fv_delta = uu____17254;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17255);_}
                       -> true
                   | uu____17262 -> false in
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
                   let uu____17407 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17407 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17494 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17533 ->
                                 let uu____17534 =
                                   let uu____17535 = is_cons head1 in
                                   Prims.op_Negation uu____17535 in
                                 FStar_Util.Inr uu____17534)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17560 =
                              let uu____17561 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17561.FStar_Syntax_Syntax.n in
                            (match uu____17560 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17579 ->
                                 let uu____17580 =
                                   let uu____17581 = is_cons head1 in
                                   Prims.op_Negation uu____17581 in
                                 FStar_Util.Inr uu____17580))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17650)::rest_a,(p1,uu____17653)::rest_p) ->
                       let uu____17697 = matches_pat t1 p1 in
                       (match uu____17697 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17746 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17852 = matches_pat scrutinee1 p1 in
                       (match uu____17852 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17892  ->
                                  let uu____17893 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17894 =
                                    let uu____17895 =
                                      FStar_List.map
                                        (fun uu____17905  ->
                                           match uu____17905 with
                                           | (uu____17910,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17895
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17893 uu____17894);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17941  ->
                                       match uu____17941 with
                                       | (bv,t1) ->
                                           let uu____17964 =
                                             let uu____17971 =
                                               let uu____17974 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____17974 in
                                             let uu____17975 =
                                               let uu____17976 =
                                                 let uu____18007 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18007, false) in
                                               Clos uu____17976 in
                                             (uu____17971, uu____17975) in
                                           uu____17964 :: env2) env1 s in
                              let uu____18124 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18124))) in
                 let uu____18125 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18125
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18146  ->
                match uu___87_18146 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18150 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18156 -> d in
      let uu____18159 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18161 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations) in
           Prims.op_Negation uu____18161) in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18159
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
            let uu___150_18186 = config s e in
            {
              steps = (uu___150_18186.steps);
              tcenv = (uu___150_18186.tcenv);
              delta_level = (uu___150_18186.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18186.strong);
              memoize_lazy = (uu___150_18186.memoize_lazy);
              normalize_pure_lets = (uu___150_18186.normalize_pure_lets)
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
      fun t  -> let uu____18211 = config s e in norm_comp uu____18211 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18224 = config [] env in norm_universe uu____18224 [] u
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
        let uu____18242 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18242 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18249 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18268 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18268.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18268.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18275 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18275
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
                  let uu___152_18284 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18284.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18284.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18284.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___153_18286 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18286.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18286.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18286.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18286.FStar_Syntax_Syntax.flags)
                  } in
            let uu___154_18287 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18287.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18287.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18289 -> c
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
        let uu____18301 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18301 in
      let uu____18308 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18308
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18312  ->
                 let uu____18313 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18313)
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
            ((let uu____18330 =
                let uu____18335 =
                  let uu____18336 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18336 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18335) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18330);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18347 = config [AllowUnboundUniverses] env in
          norm_comp uu____18347 [] c
        with
        | e ->
            ((let uu____18360 =
                let uu____18365 =
                  let uu____18366 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18366 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18365) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18360);
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
                   let uu____18403 =
                     let uu____18404 =
                       let uu____18411 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18411) in
                     FStar_Syntax_Syntax.Tm_refine uu____18404 in
                   mk uu____18403 t01.FStar_Syntax_Syntax.pos
               | uu____18416 -> t2)
          | uu____18417 -> t2 in
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
        let uu____18457 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18457 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18486 ->
                 let uu____18493 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18493 with
                  | (actuals,uu____18503,uu____18504) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18518 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18518 with
                         | (binders,args) ->
                             let uu____18535 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18535
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
      | uu____18543 ->
          let uu____18544 = FStar_Syntax_Util.head_and_args t in
          (match uu____18544 with
           | (head1,args) ->
               let uu____18581 =
                 let uu____18582 = FStar_Syntax_Subst.compress head1 in
                 uu____18582.FStar_Syntax_Syntax.n in
               (match uu____18581 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18585,thead) ->
                    let uu____18611 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18611 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18653 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18661 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18661.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18661.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18661.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18661.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18661.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18661.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18661.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18661.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18661.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18661.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18661.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18661.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18661.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18661.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18661.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18661.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18661.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18661.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18661.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18661.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18661.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18661.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18661.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18661.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18661.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18661.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18661.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18661.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18661.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18661.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18661.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18653 with
                            | (uu____18662,ty,uu____18664) ->
                                eta_expand_with_type env t ty))
                | uu____18665 ->
                    let uu____18666 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18674 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18674.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18674.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18674.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18674.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18674.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18674.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18674.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18674.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18674.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18674.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18674.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18674.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18674.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18674.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18674.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18674.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18674.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18674.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18674.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18674.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18674.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18674.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18674.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18674.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18674.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18674.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18674.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18674.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18674.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18674.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18674.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18666 with
                     | (uu____18675,ty,uu____18677) ->
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
            | (uu____18751,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18757,FStar_Util.Inl t) ->
                let uu____18763 =
                  let uu____18766 =
                    let uu____18767 =
                      let uu____18780 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18780) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18767 in
                  FStar_Syntax_Syntax.mk uu____18766 in
                uu____18763 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18784 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18784 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18811 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18866 ->
                    let uu____18867 =
                      let uu____18876 =
                        let uu____18877 = FStar_Syntax_Subst.compress t3 in
                        uu____18877.FStar_Syntax_Syntax.n in
                      (uu____18876, tc) in
                    (match uu____18867 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18902) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18939) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____18978,FStar_Util.Inl uu____18979) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19002 -> failwith "Impossible") in
              (match uu____18811 with
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
          let uu____19107 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19107 with
          | (univ_names1,binders1,tc) ->
              let uu____19165 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19165)
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
          let uu____19200 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19200 with
          | (univ_names1,binders1,tc) ->
              let uu____19260 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19260)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19293 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19293 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19321 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19321.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19321.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19321.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19321.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19342 = s in
          let uu____19343 =
            let uu____19344 =
              let uu____19353 = FStar_List.map (elim_uvars env) sigs in
              (uu____19353, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19344 in
          {
            FStar_Syntax_Syntax.sigel = uu____19343;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19342.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19342.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19342.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19342.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19370 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19370 with
           | (univ_names1,uu____19388,typ1) ->
               let uu___163_19402 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19402.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19402.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19402.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19402.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19408 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19408 with
           | (univ_names1,uu____19426,typ1) ->
               let uu___164_19440 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19440.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19440.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19440.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19440.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19474 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19474 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19497 =
                            let uu____19498 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19498 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19497 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___165_19501 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19501.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19501.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___166_19502 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19502.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19502.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19502.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19502.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19514 = s in
          let uu____19515 =
            let uu____19516 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19516 in
          {
            FStar_Syntax_Syntax.sigel = uu____19515;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19514.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19514.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19514.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19514.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19520 = elim_uvars_aux_t env us [] t in
          (match uu____19520 with
           | (us1,uu____19538,t1) ->
               let uu___168_19552 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19552.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19552.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19552.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19552.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19553 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19555 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19555 with
           | (univs1,binders,signature) ->
               let uu____19583 =
                 let uu____19592 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19592 with
                 | (univs_opening,univs2) ->
                     let uu____19619 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19619) in
               (match uu____19583 with
                | (univs_opening,univs_closing) ->
                    let uu____19636 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19642 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19643 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19642, uu____19643) in
                    (match uu____19636 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19665 =
                           match uu____19665 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19683 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19683 with
                                | (us1,t1) ->
                                    let uu____19694 =
                                      let uu____19699 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19706 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19699, uu____19706) in
                                    (match uu____19694 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19719 =
                                           let uu____19724 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19733 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19724, uu____19733) in
                                         (match uu____19719 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19749 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19749 in
                                              let uu____19750 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19750 with
                                               | (uu____19771,uu____19772,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19787 =
                                                       let uu____19788 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19788 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19787 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19793 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19793 with
                           | (uu____19806,uu____19807,t1) -> t1 in
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
                             | uu____19867 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19884 =
                               let uu____19885 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19885.FStar_Syntax_Syntax.n in
                             match uu____19884 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19944 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____19973 =
                               let uu____19974 =
                                 FStar_Syntax_Subst.compress t in
                               uu____19974.FStar_Syntax_Syntax.n in
                             match uu____19973 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____19995) ->
                                 let uu____20016 = destruct_action_body body in
                                 (match uu____20016 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20061 ->
                                 let uu____20062 = destruct_action_body t in
                                 (match uu____20062 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20111 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20111 with
                           | (action_univs,t) ->
                               let uu____20120 = destruct_action_typ_templ t in
                               (match uu____20120 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20161 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20161.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20161.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20163 = ed in
                           let uu____20164 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20165 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20166 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20167 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20168 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20169 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20170 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20171 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20172 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20173 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20174 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20175 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20176 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20177 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20163.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20163.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20164;
                             FStar_Syntax_Syntax.bind_wp = uu____20165;
                             FStar_Syntax_Syntax.if_then_else = uu____20166;
                             FStar_Syntax_Syntax.ite_wp = uu____20167;
                             FStar_Syntax_Syntax.stronger = uu____20168;
                             FStar_Syntax_Syntax.close_wp = uu____20169;
                             FStar_Syntax_Syntax.assert_p = uu____20170;
                             FStar_Syntax_Syntax.assume_p = uu____20171;
                             FStar_Syntax_Syntax.null_wp = uu____20172;
                             FStar_Syntax_Syntax.trivial = uu____20173;
                             FStar_Syntax_Syntax.repr = uu____20174;
                             FStar_Syntax_Syntax.return_repr = uu____20175;
                             FStar_Syntax_Syntax.bind_repr = uu____20176;
                             FStar_Syntax_Syntax.actions = uu____20177
                           } in
                         let uu___171_20180 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20180.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20180.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20180.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20180.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20197 =
            match uu___88_20197 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20224 = elim_uvars_aux_t env us [] t in
                (match uu____20224 with
                 | (us1,uu____20248,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___172_20267 = sub_eff in
            let uu____20268 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20271 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20267.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20267.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20268;
              FStar_Syntax_Syntax.lift = uu____20271
            } in
          let uu___173_20274 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20274.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20274.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20274.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20274.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20284 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20284 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20318 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20318.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20318.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20318.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20318.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20329 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t